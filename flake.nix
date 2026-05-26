{
  description = "muninn: indexed code search MCP server for Claude Code";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, rust-overlay, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs { inherit system overlays; };

        rustToolchain = pkgs.rust-bin.stable.latest.default.override {
          extensions = [ "rust-src" "clippy" "rustfmt" "rust-analyzer" ];
        };

        agdaWithStdlib = pkgs.agda.withPackages (ps: [ ps.standard-library ]);

        # ── ONNX Runtime static archive (Pyke prebuilt) ─────────────────────
        #
        # ort-sys with the `download-binaries` Cargo feature normally fetches
        # libonnxruntime.a from cdn.pyke.io at build time. The Nix sandbox has
        # no network, so we mirror the same archive via a fixed-output
        # `fetchurl`, decompress the raw LZMA2 stream with `xz` (64 MiB dict —
        # matches ort-sys's build/download/extract.rs: Lzma2Reader::new(reader,
        # 1 << 26, None)), and point ort-sys at the result via
        # `ORT_LIB_LOCATION`.
        #
        # Hashes come from ort-sys's `build/download/dist.txt`. Update both
        # `pykeVersion` and the per-target sha256 when ort-sys bumps the
        # Pyke release.
        pykeVersion = "1.23.2";
        pykeTargets = {
          "aarch64-darwin" = {
            target = "aarch64-apple-darwin";
            sha256 = "0897a0e1b840566a97e5a49497b02cbc204be2d006815174b639bc99731840f9";
          };
          "x86_64-linux" = {
            target = "x86_64-unknown-linux-gnu";
            sha256 = "8c57d059aaaee407812a5698d6706c79e090ad69e1a14204309e802dcbbaa35f";
          };
          "aarch64-linux" = {
            target = "aarch64-unknown-linux-gnu";
            sha256 = "c25248c32d84f228b9d584b84b31e1577e4810d46beb5e304e9fa340c000176c";
          };
        };
        pyke = pykeTargets.${system} or null;

        ortStaticLib = if pyke == null then null else
          let
            archive = pkgs.fetchurl {
              url = "https://cdn.pyke.io/0/pyke:ort-rs/ms@${pykeVersion}/${pyke.target}.tar.lzma2";
              inherit (pyke) sha256;
            };
          in pkgs.runCommandLocal "onnxruntime-pyke-${pykeVersion}-${pyke.target}" {
            nativeBuildInputs = [ pkgs.xz pkgs.gnutar ];
          } ''
            mkdir -p $out
            xz --format=raw --lzma2=dict=64MiB -d < ${archive} | tar -x -C $out
          '';

        # Shared between both packages.
        commonAttrs = {
          version = "0.1.1";
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;
          # Tests need an embedding model + Postgres; run them in the dev
          # shell via `cargo nextest` instead.
          doCheck = false;
        };

        # ── muninn (dynamic) ────────────────────────────────────────────────
        #
        # Links dynamically against nixpkgs's libonnxruntime. Smaller binary
        # but its load commands reference /nix/store/.../libonnxruntime.dylib,
        # so it only works on a machine where that path is materialised — use
        # `nix profile install .` so Nix keeps a GC root for it.
        muninn = pkgs.rustPlatform.buildRustPackage (commonAttrs // {
          pname = "muninn";
          nativeBuildInputs = [ pkgs.pkg-config ];
          buildInputs = [ pkgs.openssl pkgs.onnxruntime ];
          ORT_LIB_LOCATION = "${pkgs.onnxruntime}/lib";
          ORT_PREFER_DYNAMIC_LINK = "1";
          # nixpkgs's libonnxruntime has install_name = @rpath/...; bake the
          # store path into the binary's RUNPATH so dyld can find it at
          # runtime without a wrapper.
          RUSTFLAGS = "-C link-arg=-Wl,-rpath,${pkgs.onnxruntime}/lib";
        });

        # ── muninn-static ───────────────────────────────────────────────────
        #
        # Statically links libonnxruntime.a from the pyke archive, plus
        # openssl from `pkgsStatic`. The resulting binary has no Nix-store
        # references — only Apple's system frameworks, which must link
        # dynamically on darwin (mandated by Apple, same as any macOS binary).
        #
        # Uses `pkgsStatic.rustPlatform.buildRustPackage` so the linker
        # prefers static archives where possible (notably avoids leaking a
        # /nix/store/.../libiconv.dylib reference that plain `rustPlatform`
        # produces).
        muninnStatic = if ortStaticLib == null
          then throw "muninn-static: no Pyke onnxruntime prebuilt for system '${system}'. Build directly with `cargo build --release`."
          else pkgs.pkgsStatic.rustPlatform.buildRustPackage (commonAttrs // {
            pname = "muninn-static";
            nativeBuildInputs = [ pkgs.pkgsStatic.pkg-config ];
            buildInputs = [ pkgs.pkgsStatic.openssl ];
            OPENSSL_STATIC = "1";
            OPENSSL_NO_VENDOR = "1";
            ORT_LIB_LOCATION = "${ortStaticLib}";
          });

      in
      {
        packages = {
          default = muninn;
          muninn = muninn;
          muninn-static = muninnStatic;
        };

        devShells.default = pkgs.mkShell {
          name = "muninn-dev";

          packages = [
            rustToolchain
            pkgs.cargo-watch
            pkgs.cargo-nextest

            pkgs.sqlx-cli
            pkgs.postgresql_16  # psql client only

            agdaWithStdlib

            pkgs.pkg-config
            pkgs.openssl

            pkgs.just
            pkgs.git
          ];

          shellHook = ''
            export DATABASE_URL="''${DATABASE_URL:-postgresql://localhost/muninn_dev}"
            export TEST_DATABASE_URL="''${TEST_DATABASE_URL:-postgresql://localhost/muninn_test}"

            echo "muninn dev shell"
            echo "  Rust:  $(rustc --version)"
            echo "  Agda:  $(agda --version)"
            echo "  DATABASE_URL=$DATABASE_URL"
          '';

          PKG_CONFIG_PATH = "${pkgs.openssl.dev}/lib/pkgconfig";
        };
      }
    );
}

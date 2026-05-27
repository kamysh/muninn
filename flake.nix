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
        # crates.io currently 403s the default Nix curl User-Agent for its
        # `api/v1/crates/.../download` endpoint. Set a contact-bearing UA on
        # any fetchurl that points at crates.io so rustPlatform's per-crate
        # downloads succeed. Untouched for every other URL.
        cratesIoUa = "muninn-build (https://github.com/kamysh/muninn)";
        cratesIoUaOverlay = (final: prev: {
          fetchurl = args:
            let
              urls = args.urls or (if args ? url then [ args.url ] else [ ]);
              hitsCratesIo = builtins.any
                (u: prev.lib.hasPrefix "https://crates.io/" u
                  || prev.lib.hasPrefix "http://crates.io/" u)
                urls;
            in
            if hitsCratesIo
            then prev.fetchurl (args // {
              curlOptsList = (args.curlOptsList or [ ]) ++ [ "-A" cratesIoUa ];
            })
            else prev.fetchurl args;
        });
        overlays = [ (import rust-overlay) cratesIoUaOverlay ];
        pkgs = import nixpkgs { inherit system overlays; };

        rustToolchain = pkgs.rust-bin.stable.latest.default.override {
          extensions = [ "rust-src" "clippy" "rustfmt" "rust-analyzer" ];
        };

        agdaWithStdlib = pkgs.agda.withPackages (ps: [ ps.standard-library ]);

        # Shared between both packages.
        commonAttrs = {
          version = "0.1.13";
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;
          # Tests need a Postgres + downloaded model; run them in the dev
          # shell via `cargo nextest` instead.
          doCheck = false;
        };

        # OpenSSL note: muninn itself uses rustls for all TLS (reqwest +
        # sqlx). But tessera-embeddings → hf-hub pulls native-tls via its
        # default features (Cargo feature unification is additive, so we
        # can't disable it from below without vendoring/patching hf-hub).
        # native-tls is dead code at runtime — our code paths never reach
        # it — but `openssl-sys`'s build script still requires a system
        # OpenSSL to link against on non-darwin targets. So we keep openssl
        # in buildInputs; the link unit is present but unused.

        # ── muninn (default Nix install) ────────────────────────────────────
        #
        # Plain rustPlatform build. The local embedding backend is pure-Rust
        # (tessera-embeddings + candle), so there is no libonnxruntime or
        # other native runtime dep to wire up.
        muninn = pkgs.rustPlatform.buildRustPackage (commonAttrs // {
          pname = "muninn";
          nativeBuildInputs = [ pkgs.pkg-config ];
          buildInputs = [ pkgs.openssl ];
        });

        # ── muninn-static ───────────────────────────────────────────────────
        #
        # Same code, built under `pkgsStatic.rustPlatform` so the linker
        # prefers static archives — drops the /nix/store/.../libiconv.dylib
        # reference plain `rustPlatform` leaves on darwin. Result is portable
        # (only Apple system frameworks remain on darwin; nothing dynamic
        # on Linux musl).
        muninnStatic = pkgs.pkgsStatic.rustPlatform.buildRustPackage (commonAttrs // {
          pname = "muninn-static";
          nativeBuildInputs = [ pkgs.pkgsStatic.pkg-config ];
          buildInputs = [ pkgs.pkgsStatic.openssl ];
          OPENSSL_STATIC = "1";
          OPENSSL_NO_VENDOR = "1";
          # pkgsStatic defaults to -static-pie, but pkgsStatic's libstdc++.a
          # (pulled in by C++ deps) is built without -fPIC, so the linker
          # rejects R_X86_64_32S relocations against it. Drop PIE on
          # x86_64-linux. aarch64-linux happens not to hit this; darwin
          # uses libc++ which links cleanly.
          RUSTFLAGS = if system == "x86_64-linux" then "-C relocation-model=static" else "";
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
        };
      }
    );
}

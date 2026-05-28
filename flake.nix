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
        # crates.io's data-access filter 403s the default UA nixpkgs's
        # `fetchurl` sends on linux (darwin's curl slips through). Reproduces on
        # any linux machine with a cold store. Inject a contact-bearing UA on
        # crates.io URLs so rustPlatform's per-crate downloads succeed; every
        # other fetchurl is untouched.
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

        # The local embedding backend is model2vec (static embeddings) —
        # pure-Rust (safetensors + tokenizers/fancy-regex + ndarray). No ONNX
        # runtime, no Pyke archive, no openssl, no C/C++ deps. So both packages
        # are plain rustPlatform builds with nothing to wire up.
        commonAttrs = {
          version = "0.1.16";
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;
          nativeBuildInputs = [ pkgs.pkg-config ];
          # Tests need a Postgres + downloaded model; run them in the dev
          # shell via `cargo nextest` instead.
          doCheck = false;
        };

        # Nix-managed install (may carry a few /nix/store refs, e.g. libiconv
        # on darwin). Use `nix profile install .` to keep them as a GC root.
        muninn = pkgs.rustPlatform.buildRustPackage (commonAttrs // {
          pname = "muninn";
        });

        # Portable static build: pkgsStatic links everything reachable
        # statically — no /nix/store refs (only Apple system frameworks on
        # darwin; fully static on linux musl). Pure-Rust deps mean no openssl,
        # no libstdc++, hence no PIE workaround or glibc stubs needed.
        muninnStatic = pkgs.pkgsStatic.rustPlatform.buildRustPackage (commonAttrs // {
          pname = "muninn-static";
          nativeBuildInputs = [ pkgs.pkgsStatic.pkg-config ];
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

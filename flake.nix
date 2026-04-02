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

        # agda.withPackages wraps the binary and registers stdlib automatically
        agdaWithStdlib = pkgs.agda.withPackages (ps: [ ps.standard-library ]);

        # Dynamically linked (default) — depends on Nix store at runtime.
        # Install via `nix profile install` to keep GC roots intact.
        muninn = pkgs.rustPlatform.buildRustPackage {
          pname = "muninn";
          version = "0.1.0";
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;
          nativeBuildInputs = [ pkgs.pkg-config pkgs.makeWrapper ];
          buildInputs = [ pkgs.openssl pkgs.onnxruntime ];
          postInstall = ''
            for bin in muninn muninn-index muninn-mcp; do
              if [ -x "$out/bin/$bin" ]; then
                wrapProgram "$out/bin/$bin" \
                  --set ORT_DYLIB_PATH "${pkgs.onnxruntime}/lib/libonnxruntime.so"
              fi
            done
          '';
        };

        # Fully static build via musl — safe to copy anywhere, no Nix store deps.
        muninnStatic = pkgs.pkgsStatic.rustPlatform.buildRustPackage {
          pname = "muninn-static";
          version = "0.1.0";
          src = ./.;
          cargoLock.lockFile = ./Cargo.lock;
          nativeBuildInputs = [ pkgs.pkgsStatic.pkg-config ];
          buildInputs = [ pkgs.pkgsStatic.openssl ];
          OPENSSL_STATIC = "1";
          OPENSSL_NO_VENDOR = "1";
        };

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
            # Rust
            rustToolchain
            pkgs.cargo-watch
            pkgs.cargo-nextest

            # Database client tools (server assumed external)
            pkgs.sqlx-cli
            pkgs.postgresql_16  # psql client only

            # Formal spec
            agdaWithStdlib

            # Build deps for reqwest/openssl
            pkgs.pkg-config
            pkgs.openssl
            pkgs.onnxruntime

            # Dev utilities
            pkgs.just
            pkgs.git
          ];

          shellHook = ''
            export DATABASE_URL="''${DATABASE_URL:-postgresql://localhost/muninn_dev}"
            export TEST_DATABASE_URL="''${TEST_DATABASE_URL:-postgresql://localhost/muninn_test}"
            export ORT_DYLIB_PATH="${pkgs.onnxruntime}/lib/libonnxruntime.so"

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

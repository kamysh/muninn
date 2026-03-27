{
  description = "ai-mem: indexed code search MCP server for Claude Code";

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

        agdaWithStdlib = pkgs.agda.withPackages (ps: [
          ps.standard-library
        ]);

      in
      {
        devShells.default = pkgs.mkShell {
          name = "ai-mem-dev";

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

            # Dev utilities
            pkgs.just
            pkgs.git
          ];

          shellHook = ''
            export DATABASE_URL="''${DATABASE_URL:-postgresql://localhost/ai_mem_dev}"
            export TEST_DATABASE_URL="''${TEST_DATABASE_URL:-postgresql://localhost/ai_mem_test}"

            echo "ai-mem dev shell"
            echo "  Rust:  $(rustc --version)"
            echo "  Agda:  $(agda --version)"
            echo "  DATABASE_URL=$DATABASE_URL"
          '';

          PKG_CONFIG_PATH = "${pkgs.openssl.dev}/lib/pkgconfig";
        };
      }
    );
}
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

        # Apache AGE - graph extension for PostgreSQL
        # Not yet in nixpkgs; built from source against postgresql_16
        apacheAge = pkgs.stdenv.mkDerivation rec {
          pname = "apache-age";
          version = "1.5.0";

          src = pkgs.fetchFromGitHub {
            owner = "apache";
            repo = "age";
            rev = "PG16/v${version}-rc0";
            hash = "sha256-AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA=";
            # ^ Run `nix develop` once; nix will print the correct hash.
          };

          nativeBuildInputs = [ pkgs.postgresql_16 pkgs.bison pkgs.flex ];
          buildInputs = [ pkgs.postgresql_16 ];

          makeFlags = [ "USE_PGXS=1" ];

          installPhase = ''
            install -D age.so $out/lib/postgresql/age.so
            install -D age.control $out/share/postgresql/extension/age.control
            install -D sql/age--${version}.sql \
              $out/share/postgresql/extension/age--${version}.sql
          '';
        };

        # PostgreSQL 16 with pgvector bundled; AGE loaded separately at runtime
        postgresWithExtensions = pkgs.postgresql_16.withPackages (ps: [
          ps.pgvector
        ]);

        # Agda with standard library
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
            pkgs.cargo-nextest   # faster test runner

            # Database
            postgresWithExtensions
            pkgs.sqlx-cli

            # Formal spec
            agdaWithStdlib

            # Build deps
            pkgs.pkg-config
            pkgs.openssl
            pkgs.libiconv

            # Dev utilities
            pkgs.just            # task runner (optional Justfile)
            pkgs.git
          ];

          # Expose AGE extension path so PostgreSQL can find it at runtime
          shellHook = ''
            export AGE_EXTENSION_DIR="${apacheAge}/lib/postgresql"
            export AGE_SHARE_DIR="${apacheAge}/share/postgresql/extension"

            # Point sqlx to a local dev database
            export DATABASE_URL="''${DATABASE_URL:-postgresql://localhost/ai_mem_dev}"
            export TEST_DATABASE_URL="''${TEST_DATABASE_URL:-postgresql://localhost/ai_mem_test}"

            echo "ai-mem dev shell"
            echo "  Rust:     $(rustc --version)"
            echo "  Postgres: $(postgres --version)"
            echo "  Agda:     $(agda --version)"
            echo ""
            echo "  DATABASE_URL=$DATABASE_URL"
            echo "  To start postgres: pg_ctl -D \$PGDATA start"
          '';

          # Ensure OpenSSL is found by the reqwest crate
          PKG_CONFIG_PATH = "${pkgs.openssl.dev}/lib/pkgconfig";
        };
      }
    );
}
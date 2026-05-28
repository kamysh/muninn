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
        # crates.io's data-access filter currently 403s the default UA sent
        # by nixpkgs's `fetchurl` on linux (likely the linux-shipped curl
        # version triggers a deny heuristic; darwin's curl slips through).
        # Reproduces on any linux machine with `nix build .#muninn-static`
        # from a cold store — not GH-runner-specific. This overlay injects
        # a contact-bearing UA on any fetchurl pointing at crates.io so
        # rustPlatform's per-crate downloads succeed. Darwin doesn't need
        # the override but applying it everywhere is harmless and keeps
        # the flake portable. Every non-crates.io fetchurl is untouched.
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
        pykeVersion = "1.24.2";
        pykeTargets = {
          "aarch64-darwin" = {
            target = "aarch64-apple-darwin";
            sha256 = "612739f75438dc0a075461e1fb454226b4a1eb175e60a7271ba966bbbb972cd4";
          };
          "x86_64-linux" = {
            target = "x86_64-unknown-linux-gnu";
            sha256 = "acc1cba79c337594ead1d88ca72516147aa60054c84217b53399a31caa5ba671";
          };
          "aarch64-linux" = {
            target = "aarch64-unknown-linux-gnu";
            sha256 = "7e4f5fec4494cbf578c4e28082b0229c42f735523f584259028dde96acf3b092";
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

        # ── glibc stubs for aarch64-linux musl builds ────────────────────────
        #
        # The Pyke aarch64-unknown-linux-gnu archive contains objects compiled
        # with glibc GCC that reference symbols absent from musl:
        #   • _FORTIFY_SOURCE=2 wrappers: __memset_chk, __read_chk, __vsnprintf_chk, etc.
        #   • glibc 2.38+ C23 aliases: __isoc23_strtol and family
        #   • glibc large-file aliases: stat64, fstat64, lstat64
        #
        # We provide pass-through stubs for all of these on both aarch64-linux and
        # x86_64-linux (both Pyke targets use glibc GCC). On aarch64 we additionally
        # stub __aarch64_cas*_sync in a separate archive member: compiler_builtins
        # (Rust 1.94+) provides acq/rel/acq_rel/relax CAS and all ldadd/swp/ldclr/
        # ldset/ldeor variants but NOT sync; XNNPack init.c references cas8_sync.
        # The separate object avoids multiple-definition conflicts with compiler_builtins.
        #
        # -lc is appended after the stubs so musl is re-scanned and resolves
        # vprintf/strncat/stat referenced from our printf and stat stubs.
        glibcStubs = if system != "aarch64-linux" && system != "x86_64-linux" then null else
          pkgs.pkgsStatic.stdenv.mkDerivation {
            name = "glibc-musl-stubs";
            unpackPhase = ":";
            buildPhase = ''
              cat > stubs.c << 'EOF'
              #include <string.h>
              #include <stdio.h>
              #include <stdarg.h>
              #include <stdlib.h>
              #include <stdint.h>
              #include <unistd.h>

              /* _FORTIFY_SOURCE pass-throughs */
              char __libc_single_threaded = 0;
              void *__memcpy_chk(void *d,const void *s,size_t n,size_t ds){return memcpy(d,s,n);}
              void *__memmove_chk(void *d,const void *s,size_t n,size_t ds){return memmove(d,s,n);}
              void *__memset_chk(void *s,int c,size_t n,size_t ds){return memset(s,c,n);}
              void *__mempcpy_chk(void *d,const void *s,size_t n,size_t ds){return memcpy(d,s,n);}
              char *__strcpy_chk(char *d,const char *s,size_t ds){return strcpy(d,s);}
              char *__strncpy_chk(char *d,const char *s,size_t n,size_t ds){return strncpy(d,s,n);}
              char *__strcat_chk(char *d,const char *s,size_t ds){return strcat(d,s);}
              char *__strncat_chk(char *d,const char *s,size_t n,size_t ds){return strncat(d,s,n);}
              ssize_t __read_chk(int fd,void *buf,size_t n,size_t bs){return read(fd,buf,n);}
              int __printf_chk(int f,const char *fmt,...){va_list a;va_start(a,fmt);int r=vprintf(fmt,a);va_end(a);return r;}
              int __fprintf_chk(FILE *fp,int f,const char *fmt,...){va_list a;va_start(a,fmt);int r=vfprintf(fp,fmt,a);va_end(a);return r;}
              int __sprintf_chk(char *s,int f,size_t ss,const char *fmt,...){va_list a;va_start(a,fmt);int r=vsprintf(s,fmt,a);va_end(a);return r;}
              int __snprintf_chk(char *s,size_t n,int f,size_t ss,const char *fmt,...){va_list a;va_start(a,fmt);int r=vsnprintf(s,n,fmt,a);va_end(a);return r;}
              int __vprintf_chk(int f,const char *fmt,va_list a){return vprintf(fmt,a);}
              int __vfprintf_chk(FILE *fp,int f,const char *fmt,va_list a){return vfprintf(fp,fmt,a);}
              int __vsprintf_chk(char *s,int f,size_t ss,const char *fmt,va_list a){return vsprintf(s,fmt,a);}
              int __vsnprintf_chk(char *s,size_t n,int f,size_t ss,const char *fmt,va_list a){return vsnprintf(s,n,fmt,a);}

              /* C23 strtol-family (glibc 2.38+, absent from musl) */
              long __isoc23_strtol(const char *s,char **e,int b){return strtol(s,e,b);}
              unsigned long __isoc23_strtoul(const char *s,char **e,int b){return strtoul(s,e,b);}
              long long __isoc23_strtoll(const char *s,char **e,int b){return strtoll(s,e,b);}
              unsigned long long __isoc23_strtoull(const char *s,char **e,int b){return strtoull(s,e,b);}

              /* glibc large-file aliases (musl uses 64-bit stat unconditionally) */
              #include <sys/stat.h>
              int stat64(const char *p,struct stat *b){return stat(p,b);}
              int fstat64(int fd,struct stat *b){return fstat(fd,b);}
              int lstat64(const char *p,struct stat *b){return lstat(p,b);}

              EOF
              $CC -c stubs.c -o stubs.o

              ${if system == "aarch64-linux" then ''
                # __aarch64_cas*_sync — separate object, pulled in independently of
                # stubs.o. compiler_builtins provides acq/rel/acq_rel/relax CAS but
                # NOT sync. XNNPack init.c references __aarch64_cas8_sync.
                # -mno-outline-atomics prevents recursive __atomic_compare_exchange_n.
                cat > cas_sync.c << 'EOF'
                #include <stdint.h>
                #define CAS_SYNC(W,T) \
                T __aarch64_cas##W##_sync(T o,T n,volatile T*p){\
                  __atomic_compare_exchange_n(p,&o,n,0,__ATOMIC_SEQ_CST,__ATOMIC_SEQ_CST);\
                  return o;}
                CAS_SYNC(1,uint8_t)
                CAS_SYNC(2,uint16_t)
                CAS_SYNC(4,uint32_t)
                CAS_SYNC(8,uint64_t)
                EOF
                $CC -c cas_sync.c -o cas_sync.o -mno-outline-atomics
                $AR rcs libglibc_stubs.a stubs.o cas_sync.o
              '' else ''
                $AR rcs libglibc_stubs.a stubs.o
              ''}
            '';
            installPhase = ''
              mkdir -p $out/lib
              cp libglibc_stubs.a $out/lib/
            '';
          };

        # Shared between both packages.
        commonAttrs = {
          version = "0.1.15";
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
            buildInputs = [ pkgs.pkgsStatic.openssl ]
              ++ (if glibcStubs != null then [ glibcStubs ] else []);
            OPENSSL_STATIC = "1";
            OPENSSL_NO_VENDOR = "1";
            ORT_LIB_LOCATION = "${ortStaticLib}";
            RUSTFLAGS =
              # aarch64-linux: glibc-stub archive for symbols absent from musl
              (if glibcStubs != null
                then "-C link-arg=-L${glibcStubs}/lib -C link-arg=-lglibc_stubs -C link-arg=-lc"
                else "") +
              # x86_64-linux: pkgsStatic defaults to -static-pie, but libstdc++.a
              # (pulled in by ORT's C++ runtime) is not compiled -fPIC.
              # -C relocation-model=static disables PIE for this target.
              (if system == "x86_64-linux" then " -C relocation-model=static" else "");
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

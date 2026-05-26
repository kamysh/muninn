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

        # ── glibc stubs for aarch64-linux musl builds ────────────────────────
        #
        # The Pyke aarch64-unknown-linux-gnu archive contains objects compiled
        # with glibc GCC that reference symbols absent from musl:
        #   • _FORTIFY_SOURCE=2 wrappers: __memset_chk, __read_chk, __vsnprintf_chk, etc.
        #   • glibc 2.38+ C23 aliases: __isoc23_strtol and family
        #   • glibc large-file aliases: stat64, fstat64, lstat64
        #
        # We provide pass-through stubs for all of these. The outline-atomic
        # functions (__aarch64_cas*, __aarch64_swp*, __aarch64_ldadd*) are NOT
        # stubbed here — Rust's compiler_builtins (1.94+) already provides them
        # for aarch64-unknown-linux-musl via inline LDXR/STLXR, without getauxval.
        #
        # -lc is appended after the stubs so musl is re-scanned and resolves
        # vprintf/strncat/stat referenced from our printf and stat stubs.
        glibcStubs = if system != "aarch64-linux" then null else
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

              /* GCC aarch64 outline-atomics — CAS only.
                 compiler_builtins (Rust 1.94+) provides ldadd/swp/ldclr/ldset/ldeor
                 but NOT cas. Compiled with -mno-outline-atomics so the
                 __atomic_compare_exchange_n calls below expand to LDXR/STLXR
                 rather than recursing back into __aarch64_cas*. */
              #ifdef __aarch64__
              #define CAS(W,T,SUC,FAIL,SFX) \
              T __aarch64_cas##W##_##SFX(T o,T n,volatile T*p){\
                __atomic_compare_exchange_n(p,&o,n,0,SUC,FAIL);return o;}
              CAS(1,uint8_t,__ATOMIC_RELAXED,__ATOMIC_RELAXED,relax)
              CAS(2,uint16_t,__ATOMIC_RELAXED,__ATOMIC_RELAXED,relax)
              CAS(4,uint32_t,__ATOMIC_RELAXED,__ATOMIC_RELAXED,relax)
              CAS(8,uint64_t,__ATOMIC_RELAXED,__ATOMIC_RELAXED,relax)
              CAS(1,uint8_t,__ATOMIC_ACQUIRE,__ATOMIC_RELAXED,acq)
              CAS(2,uint16_t,__ATOMIC_ACQUIRE,__ATOMIC_RELAXED,acq)
              CAS(4,uint32_t,__ATOMIC_ACQUIRE,__ATOMIC_RELAXED,acq)
              CAS(8,uint64_t,__ATOMIC_ACQUIRE,__ATOMIC_RELAXED,acq)
              CAS(1,uint8_t,__ATOMIC_RELEASE,__ATOMIC_RELAXED,rel)
              CAS(2,uint16_t,__ATOMIC_RELEASE,__ATOMIC_RELAXED,rel)
              CAS(4,uint32_t,__ATOMIC_RELEASE,__ATOMIC_RELAXED,rel)
              CAS(8,uint64_t,__ATOMIC_RELEASE,__ATOMIC_RELAXED,rel)
              CAS(1,uint8_t,__ATOMIC_ACQ_REL,__ATOMIC_RELAXED,acq_rel)
              CAS(2,uint16_t,__ATOMIC_ACQ_REL,__ATOMIC_RELAXED,acq_rel)
              CAS(4,uint32_t,__ATOMIC_ACQ_REL,__ATOMIC_RELAXED,acq_rel)
              CAS(8,uint64_t,__ATOMIC_ACQ_REL,__ATOMIC_RELAXED,acq_rel)
              CAS(1,uint8_t,__ATOMIC_SEQ_CST,__ATOMIC_SEQ_CST,sync)
              CAS(2,uint16_t,__ATOMIC_SEQ_CST,__ATOMIC_SEQ_CST,sync)
              CAS(4,uint32_t,__ATOMIC_SEQ_CST,__ATOMIC_SEQ_CST,sync)
              CAS(8,uint64_t,__ATOMIC_SEQ_CST,__ATOMIC_SEQ_CST,sync)
              #endif
              EOF
              $CC -c stubs.c -o stubs.o -mno-outline-atomics
              $AR rcs libglibc_stubs.a stubs.o
            '';
            installPhase = ''
              mkdir -p $out/lib
              cp libglibc_stubs.a $out/lib/
            '';
          };

        # Shared between both packages.
        commonAttrs = {
          version = "0.1.7";
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
            RUSTFLAGS = if glibcStubs != null
              then "-C link-arg=-L${glibcStubs}/lib -C link-arg=-lglibc_stubs -C link-arg=-lc"
              else "";
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

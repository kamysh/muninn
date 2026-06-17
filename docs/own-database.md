<!-- AI CODING AGENTS: STOP. This is the HUMAN install guide. Your procedure is
     ../AGENTS.md (repo root) — same end state, but with explicit variables,
     verify-after-each-step, and idempotent state detection. Do not follow the
     steps below. -->

> ⛔ **AI coding agents — this guide is not for you.** It is the *human* install
> path. Your procedure is **[AGENTS.md](../AGENTS.md)** — follow that instead.

# Using your own PostgreSQL instance

If you already have a PostgreSQL 16+ instance — local, self-hosted, or managed — follow this guide. The binary download, daemon setup, and Claude Code integration steps are the same as `docs/get-started.md`; only the database preparation differs.

## Requirements

- PostgreSQL 16 or later (not 15 — Apache AGE requires PG16)
- Superuser access for the initial setup only (to install extensions and grant privileges); day-to-day muninn use is as a normal role
- Three extensions: **pgvector**, **Apache AGE**, **pgcrypto**

The first migration (run automatically the first time any muninn binary connects — e.g. `muninn init`) checks that all three extensions are installed and that your user has the necessary permissions. It will print a clear error if anything is missing.

---

## Option A — Homebrew on macOS

### Install pgvector

```bash
brew install pgvector
```

This installs pgvector into the Homebrew-managed PostgreSQL instance.

### Install Apache AGE

**Important:** `apache-age` may not be in the default Homebrew tap. Try:

```bash
brew install apache-age
```

If that fails with "No available formula", build from source. You will need Xcode command-line tools:

```bash
xcode-select --install
```

Then:

```bash
git clone https://github.com/apache/age.git
cd age
git checkout PG16/v1.6.0-rc0   # must match your PostgreSQL major version
make
make install
```

To confirm your PostgreSQL major version:

```bash
psql --version | awk '{print $3}' | cut -d. -f1
```

Verify the AGE install (macOS uses `.dylib`, not `.so`):

```bash
ls "$(pg_config --pkglibdir)/age.dylib"
```

If the file exists, the install succeeded.

### Enable AGE in postgresql.conf

AGE must be listed in `shared_preload_libraries`. Find your `postgresql.conf`:

```bash
psql -c 'SHOW config_file;'
```

> **Homebrew note:** On Homebrew, `psql` connects as your macOS username by default — not as `postgres`. If you run `psql -U postgres` you will get an authentication error. Use `psql` or `psql -d postgres` instead.

Add or extend the `shared_preload_libraries` line:

```
shared_preload_libraries = 'age'
# If other libraries are already listed, append:
# shared_preload_libraries = 'pg_stat_statements,age'
```

Restart PostgreSQL:

```bash
brew services restart postgresql@16
# If you installed the unversioned formula:
# brew services restart postgresql
```

### Connect to PostgreSQL (Homebrew)

On Homebrew, your macOS username is the PostgreSQL superuser — not `postgres`. Connect with:

```bash
psql -d postgres          # connects as $(whoami) to database "postgres"
```

Skip ahead to [Create the database and user](#create-the-database-and-user).

---

## Option B — Linux (APT-based, e.g. Ubuntu/Debian)

### Install pgvector

```bash
sudo apt install postgresql-16-pgvector
```

### Install Apache AGE

AGE is not in the default APT repositories. Build from source:

```bash
sudo apt install postgresql-server-dev-16 build-essential flex bison

git clone https://github.com/apache/age.git
cd age
git checkout PG16/v1.6.0-rc0
make
sudo make install
```

Verify:

```bash
ls "$(pg_config --pkglibdir)/age.so"
```

### Enable AGE in postgresql.conf

```bash
sudo grep -n shared_preload /etc/postgresql/16/main/postgresql.conf
```

Add or extend:

```
shared_preload_libraries = 'age'
```

Restart:

```bash
sudo systemctl restart postgresql
```

### Connect to PostgreSQL

```bash
sudo -u postgres psql
```

---

## Option C — Managed PostgreSQL (RDS, Cloud SQL, Supabase, etc.)

Check your provider's extension support before proceeding.

**pgvector:** Available as a managed extension on Amazon RDS, Google Cloud SQL, Azure Database for PostgreSQL, and Neon. Enable via your provider's console or `CREATE EXTENSION vector;`.

**Apache AGE:** Available on Amazon RDS for PostgreSQL (as `age`) and Google Cloud SQL. **Not available on Supabase or Azure Database for PostgreSQL** as of this writing. If your provider does not support AGE, muninn's structural search (call graphs, symbol relationships) will not work, but full-text and semantic search will work normally. The first migration will fail if AGE is absent — you will see a clear error message.

**`shared_preload_libraries`:** On managed instances you cannot edit `postgresql.conf` directly. Providers that support AGE typically have it pre-loaded; no action required on your part.

**Connecting:** Your host will be the provider endpoint (not `localhost`). SSL is typically required.

In `~/.pgpass`:

```
db.abc123.rds.amazonaws.com:5432:muninn:alice:yourpassword
```

In `~/.config/muninn/config.toml`, add under `[database]`:

```toml
[database]
ssl_mode = "require"
# For verify-full with a CA bundle:
# ssl_root_cert = "/path/to/ca.pem"
```

For connection strings with special parameters (IAM auth, Unix socket, etc.):

```toml
[database]
dsn_override = "postgresql://alice@db.abc123.rds.amazonaws.com:5432/muninn?sslmode=require"
```

---

## Create the database and user

Homebrew users: connect with `psql -d postgres`. Linux users: connect with `sudo -u postgres psql`. Managed DB users: connect via your provider's method.

```sql
-- Replace 'alice' and 'yourpassword' with your chosen values.
CREATE USER alice WITH PASSWORD 'yourpassword';
CREATE DATABASE muninn OWNER alice;

\c muninn

CREATE EXTENSION IF NOT EXISTS pgcrypto;
CREATE EXTENSION IF NOT EXISTS vector;
CREATE EXTENSION IF NOT EXISTS age;

-- AGE stores its graph metadata in the ag_catalog schema.
-- muninn needs permission to use it.
GRANT USAGE ON SCHEMA ag_catalog TO alice;
GRANT EXECUTE ON ALL FUNCTIONS IN SCHEMA ag_catalog TO alice;
\q
```

Verify everything is accessible as the muninn user (password prompt will use `~/.pgpass` if configured):

```bash
psql -h localhost -U alice -d muninn -c 'SELECT extname FROM pg_extension ORDER BY extname;'
```

Expected output:

```
   extname
-----------
 age
 pgcrypto
 plpgsql
 vector
(4 rows)
```

---

## Set up ~/.pgpass

PostgreSQL reads passwords from `~/.pgpass` so they never appear in application config files. Format: `hostname:port:database:username:password`.

For a local TCP connection:

```
localhost:5432:muninn:alice:yourpassword
```

For a Unix socket connection (socket paths vary by platform):

```
# Homebrew on Apple Silicon (M1/M2/M3):
/opt/homebrew/var/run/postgresql:5432:muninn:alice:yourpassword

# Homebrew on Intel Mac or Linux:
/var/run/postgresql:5432:muninn:alice:yourpassword
```

For managed databases:

```
db.abc123.rds.amazonaws.com:5432:muninn:alice:yourpassword
```

Set permissions — PostgreSQL ignores `~/.pgpass` if it is world-readable:

```bash
chmod 600 ~/.pgpass
```

---

## Configure and connect muninn

Run `muninn init` (no arguments opens the template in `$EDITOR`; or pass `key=value` settings non-interactively). Set the `[database]` section to point at your instance:

```toml
[database]
host   = "localhost"   # or your managed DB endpoint
port   = 5432
dbname = "muninn"
user   = "alice"
```

For managed databases, also add `ssl_mode = "require"` under `[database]`.

Save and close. muninn validates the config and applies schema migrations automatically. Migrations are idempotent — safe to re-run. Already-applied migrations are skipped.

Then follow `docs/get-started.md` from **Step 3** onward (download binaries, start daemon, connect Claude Code, add repos). The database and cloud embedding setup are the only differences from the default quickstart.

---

## Related docs

- `docs/get-started.md` — binary download, daemon setup, Claude Code integration, adding your first repo
- `docs/upgrading.md` — upgrading binaries and applying new migrations
- `docs/configuration.md` — full config file reference

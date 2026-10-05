# Custom PostgreSQL setup — advanced, not recommended

**Use [postgres-ai](https://github.com/kamysh/postgres-ai) for the recommended
installation.** It provides a compatible PostgreSQL, pgvector and Apache AGE
stack, including pgcrypto. Creating or reusing that distribution is covered by
[Getting started](get-started.md).

This document is for administrators who deliberately choose to assemble and
maintain the database stack themselves. Availability of PostgreSQL and individual
extension packages does not establish that their versions, loading behavior and
privileges work together. You take responsibility for validating that combination.

Muninn 1.0 requires **pgvector, Apache AGE and pgcrypto**; there is no supported
AGE-free fallback, even if only text/semantic search is wanted.

## Compatibility and loading

The verified development fixture uses PostgreSQL 16, AGE 1.6.0 and pgvector 0.8.1.
This is a tested combination, not a claim that AGE only supports PostgreSQL 16.
Choose an AGE build matching the server's PostgreSQL major version; see the
[official AGE downloads](https://age.apache.org/download/) and
[setup instructions](https://age.apache.org/age-manual/master/intro/setup.html).
Muninn's filtered HNSW search uses iterative scans, available in pgvector 0.8.0
and later. See [pgvector's iterative scan documentation](https://github.com/pgvector/pgvector#iterative-index-scans).

Install server extension packages using the method appropriate to your OS and
PostgreSQL installation. When building extensions, `pg_config` must select that
same server installation. A client `psql --version` alone does not establish the
server version. Check `SHOW server_version` on the intended server.

AGE must be loaded into Muninn's database sessions. Muninn sets the search path
to `public,ag_catalog` but does not issue `LOAD 'age'` on each connection. The
verified setup preloads AGE with `shared_preload_libraries = 'age'`; a database
administrator must merge that with existing preload entries and restart PostgreSQL
when needed. Do not replace other applications' preload configuration.

For managed PostgreSQL, verify that the provider supports the required AGE version,
preloading and application privileges. Do not infer AGE availability from pgvector
availability. Unsupported AGE installation blocks this application; changing the
database provider is a separate decision.

## Prepare a fresh application database

The following is an administrator procedure for a new role/database. Choose names
and credentials first. For existing resources, inspect ownership and permissions
rather than replaying creation blindly. Use `psql -v ON_ERROR_STOP=1` so errors
stop the setup. Substitute your actual names/password:

```sql
CREATE ROLE muninn LOGIN PASSWORD 'REPLACE_WITH_GENERATED_HEX_PASSWORD';
CREATE DATABASE muninn OWNER muninn;
\connect muninn
CREATE EXTENSION IF NOT EXISTS pgcrypto WITH SCHEMA public;
CREATE EXTENSION IF NOT EXISTS vector WITH SCHEMA public;
CREATE EXTENSION IF NOT EXISTS age;
GRANT USAGE, CREATE ON SCHEMA public TO muninn;
GRANT USAGE ON SCHEMA ag_catalog TO muninn;
GRANT SELECT, INSERT, UPDATE, DELETE ON ALL TABLES IN SCHEMA ag_catalog TO muninn;
GRANT EXECUTE ON ALL FUNCTIONS IN SCHEMA ag_catalog TO muninn;
GRANT USAGE ON ALL SEQUENCES IN SCHEMA ag_catalog TO muninn;
```

Muninn's application role owns its database here, allowing Kryzhen and AGE to
create their schemas. If ownership differs, the administrator must provide the
necessary database CREATE privilege and ownership of existing application objects;
a SELECT-only role is insufficient. Enable vector in `public`, as the migration
templates explicitly use `public.vector` and its operator class.

The first public migration checks extension presence and AGE schema usage. That
check is not a complete test of later graph creation/indexing permissions. Verify
first-family indexing and a structural search after setup.

## Credentials and global configuration

Add a matching entry to the application user's `~/.pgpass`, preserving other
entries, and set mode `0600`:

```text
localhost:5432:muninn:muninn:YOUR_PASSWORD
```

Muninn's own reader matches the configured host/port/database/user literally,
with `*` wildcard support. It does not implement every libpq escaped-field rule;
use simple values and a generated hexadecimal password for this setup. The same
user account must launch the CLI, daemon and local MCP process.

Install the [matching binaries](get-started.md#3-install-matching-binaries), then:

```sh
muninn init database.host=localhost database.port=5432 \
  database.dbname=muninn database.user=muninn embeddings.backend=local
```

For a remote server, use explicit host/port/database/user fields; `dsn_override`
is not implemented by the connection builder. Current SSL options do not enforce
TLS-only transport: the driver's default allows plaintext fallback, and the
connector selected by `require` disables certificate validation. A remote setup
needs a separately validated transport arrangement. Do not treat these mode names
as libpq-equivalent guarantees. See
[Configuration](configuration.md#database-connection).

## Verify and continue

Connect as the application role to the actual target:

```sh
psql -X -h localhost -p 5432 -U muninn -d muninn -c 'SHOW server_version;'
psql -X -h localhost -p 5432 -U muninn -d muninn \
  -c 'SELECT extname, extversion FROM pg_extension ORDER BY extname;'
muninn status
```

Then continue with [the watcher](get-started.md#5-run-the-watcher), explicit first
family configuration/start and the chosen agent client. Do not recreate the
database when diagnosing a connection or migration failure.

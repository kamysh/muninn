#!/usr/bin/env bash
# Explicit disposable test target. Never reads Muninn config or the user's pgpass.
set -euo pipefail
image=sha256:79fb863620098b1e443338075bb65f6775130cbcb381f115d4272719256e334d
name=muninn-persistence-test-20261004
repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo"
test_bwrap=${MUNINN_TEST_BWRAP:-bwrap}
for tool in docker psql cargo jq openssl ss timeout "$test_bwrap"; do command -v "$tool" >/dev/null; done
[[ -z $(docker ps -aq --filter "name=^/${name}$") ]] || { echo 'Container name already exists'; exit 1; }
[[ $(docker image inspect --format '{{.Id}}' "$image") == "$image" ]]
[[ -z $(ss -H -ltn 'sport = :5451') ]] || { echo 'Port 5451 is occupied'; exit 1; }
umask 077
fixture=$(mktemp -d /tmp/muninn-persistence-test-XXXXXX)
nonce=$(openssl rand -hex 16)
cleanup() {
    result=$?
    trap '' INT TERM
    trap - EXIT
    cid=$(cat "$fixture/container-id" 2>/dev/null || true)
    if [[ -n "$cid" ]]; then
        label=$(docker inspect --format '{{index .Config.Labels "muninn.persistence-test"}}' "$cid") || exit 1
        [[ "$label" == "$nonce" ]] || { echo "Cleanup identity mismatch: $fixture"; exit 1; }
        docker rm -f "$cid" >/dev/null || exit 1
        [[ -z $(docker ps -aq --filter "id=$cid") ]] || exit 1
    fi
    rm -rf -- "$fixture"
    [[ ! -e "$fixture" && -z $(ss -H -ltn 'sport = :5451') ]] || exit 1
    echo 'Cleanup verified: container absent, port free, fixture and credentials removed.'
    exit "$result"
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
echo "Fixture directory: $fixture"
admin_password=$(openssl rand -hex 32)
app_password=$(openssl rand -hex 32)
printf '%s\n' "$admin_password" > "$fixture/admin-password"
# Private parent protects the host file; container UID 999 needs read access.
chmod 644 "$fixture/admin-password"
printf '127.0.0.1:5451:*:postgres:%s\n' "$admin_password" > "$fixture/pgpass"
psql_test() {
    env -u PGSERVICE -u PGSERVICEFILE -u PGOPTIONS -u PGPASSWORD \
        PGPASSFILE="$fixture/pgpass" PGCONNECT_TIMEOUT=2 \
        psql -X -w -v ON_ERROR_STOP=1 -h 127.0.0.1 -p 5451 -U postgres "$@"
}
docker create --name "$name" --cidfile "$fixture/container-id" \
    --label "muninn.persistence-test=$nonce" --user 999:999 --memory 1g \
    --tmpfs /var/lib/postgresql/data:rw,size=512m,uid=999,gid=999,mode=0700 \
    --publish 127.0.0.1:5451:5432 \
    --mount "type=bind,src=$fixture/admin-password,dst=/run/admin-password,readonly" \
    --entrypoint /bin/bash "$image" -c '
        initdb -D /var/lib/postgresql/data --username=postgres --auth=scram-sha-256 --pwfile=/run/admin-password &&
        printf "host all all all scram-sha-256\n" >> /var/lib/postgresql/data/pg_hba.conf &&
        exec postgres -D /var/lib/postgresql/data -c listen_addresses="*" -c port=5432 \
            -c shared_preload_libraries=age -c unix_socket_directories=/var/lib/postgresql/data \
            -c search_path=public,ag_catalog -c shared_buffers=64MB -c max_connections=30
    ' >/dev/null
cid=$(cat "$fixture/container-id")
docker inspect "$cid" | jq -e --arg image "$image" --arg nonce "$nonce" '
    .[0] | .Image == $image and .Config.Labels["muninn.persistence-test"] == $nonce
    and .HostConfig.PortBindings["5432/tcp"] == [{HostIp:"127.0.0.1",HostPort:"5451"}]
    and ([.Mounts[] | select(.Type == "volume")] | length == 0)' >/dev/null
jq -n --arg container "$cid" --arg image "$image" --arg run_id "$nonce" \
    '{container:$container,image:$image,run_id:$run_id,port:5451,database:"muninn_persistence_test"}' > "$fixture/manifest.json"
echo "Starting disposable container $name on port 5451"
docker start "$cid" >/dev/null
ready=false
for ((attempt=0; attempt<60; attempt++)); do
    if psql_test -d postgres -Atc 'SELECT 1' >/dev/null 2>&1; then ready=true; break; fi
    sleep 1
done
[[ "$ready" == true ]] || { docker logs --tail 30 "$cid"; exit 1; }
echo 'Bootstrapping test database, non-superuser role, and extensions'
psql_test -d postgres >/dev/null <<SQL
CREATE ROLE muninn_persistence_test LOGIN NOSUPERUSER NOCREATEDB NOCREATEROLE PASSWORD '$app_password';
CREATE DATABASE muninn_persistence_test OWNER muninn_persistence_test;
SQL
psql_test -d muninn_persistence_test >/dev/null <<SQL
CREATE EXTENSION pgcrypto WITH SCHEMA public VERSION '1.3';
CREATE EXTENSION vector WITH SCHEMA public VERSION '0.8.1';
CREATE EXTENSION age VERSION '1.6.0';
GRANT USAGE, CREATE ON SCHEMA public TO muninn_persistence_test;
GRANT USAGE ON SCHEMA ag_catalog TO muninn_persistence_test;
GRANT SELECT, INSERT, UPDATE, DELETE ON ALL TABLES IN SCHEMA ag_catalog TO muninn_persistence_test;
GRANT EXECUTE ON ALL FUNCTIONS IN SCHEMA ag_catalog TO muninn_persistence_test;
GRANT USAGE ON ALL SEQUENCES IN SCHEMA ag_catalog TO muninn_persistence_test;
CREATE TABLE public.muninn_persistence_test_run (run_id text PRIMARY KEY);
INSERT INTO public.muninn_persistence_test_run VALUES ('$nonce');
GRANT SELECT ON public.muninn_persistence_test_run TO muninn_persistence_test;
SQL
# Supply the secret over stdin, never in process arguments.
printf '%s' "$app_password" | jq -Rs --arg run_id "$nonce" --arg fixture_root "$fixture" \
    '{host:"127.0.0.1",port:5451,database:"muninn_persistence_test",user:"muninn_persistence_test",password:.,run_id:$run_id,fixture_root:$fixture_root}' > "$fixture/connection.json"
printf '127.0.0.1:5451:muninn_persistence_test:muninn_persistence_test:%s\n' "$app_password" > "$fixture/client-pgpass"
unset admin_password app_password
# Present only disposable credentials at the application's existing lookup path.
# The bind mount exists only in each test process's private mount namespace;
# neither HOME nor the host user's .pgpass is changed.
test_cargo() {
    test_filter=$1
    shift
    # Build normally; only executable test processes need the credential view.
    cargo test "$@" --locked --offline --no-run --message-format=json > "$fixture/build.json"
    mapfile -t test_executables < <(jq -r 'select(.reason == "compiler-artifact" and .profile.test and .executable != null) | .executable' "$fixture/build.json")
    [[ ${#test_executables[@]} == 1 ]] || { echo 'Expected exactly one test executable'; exit 1; }
    MUNINN_PERSISTENCE_TEST_CONFIG="$fixture/connection.json" \
        "$test_bwrap" --die-with-parent --bind / / --dev /dev \
        --ro-bind "$fixture/client-pgpass" "$HOME/.pgpass" -- \
        timeout --signal=TERM --kill-after=10s 600s "${test_executables[0]}" "$test_filter" --ignored --nocapture
}
# An explicitly supplied private verifier reuses this same guarded DB lifecycle.
if (( $# )); then
    [[ "$1" = /* && -x "$1" ]] || { echo 'Verifier must be an absolute executable path'; exit 1; }
    MUNINN_PERSISTENCE_TEST_CONFIG="$fixture/connection.json" \
        "$test_bwrap" --die-with-parent --bind / / --dev /dev \
        --ro-bind "$fixture/client-pgpass" "$HOME/.pgpass" -- \
        timeout --signal=TERM --kill-after=10s 600s "$@"
else
    test_cargo family_persistence -p muninn-core --test family_persistence
    test_cargo tui::tests::persistence -p muninn --bin muninn
    test_cargo tests::policy_dispatch -p muninn-index --bin muninn-index
fi

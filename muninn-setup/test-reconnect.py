#!/usr/bin/env python3
"""Run only through test-persistence.sh against its disposable database."""
import json
import os
import select
import subprocess
import tempfile
import time
from pathlib import Path

target = json.loads(Path(os.environ["MUNINN_PERSISTENCE_TEST_CONFIG"]).read_text())
assert (target["host"], target["port"], target["database"], target["user"]) == (
    "127.0.0.1", 5451, "muninn_persistence_test", "muninn_persistence_test"
)
root = Path(__file__).resolve().parent.parent
cli_log = tempfile.NamedTemporaryFile(prefix="muninn-reconnect-cli-", suffix=".log", dir="/tmp", delete=False)
cli_log.close()

def sql(query):
    return subprocess.check_output([
        "psql", "-X", "-w", "-v", "ON_ERROR_STOP=1", "-At",
        "-h", target["host"], "-p", str(target["port"]), "-U", target["user"],
        "-d", target["database"], "-c", query,
    ], text=True).strip()

def admin_sql(query):
    env = os.environ.copy()
    env["PGPASSFILE"] = str(Path(target["fixture_root"]) / "pgpass")
    return subprocess.check_output([
        "psql", "-X", "-w", "-v", "ON_ERROR_STOP=1", "-At",
        "-h", target["host"], "-p", str(target["port"]), "-U", "postgres",
        "-d", target["database"], "-c", query,
    ], text=True, env=env).strip()

def eventually(predicate, description):
    deadline = time.monotonic() + 20
    while time.monotonic() < deadline:
        if predicate():
            return
        time.sleep(0.1)
    raise AssertionError(f"timed out waiting for {description}")

def pids(name):
    output = sql("SELECT pid FROM pg_stat_activity WHERE application_name='" + name + "' ORDER BY pid")
    return set(output.splitlines()) if output else set()

def cli(*args, request=None):
    result = subprocess.run(
        [str(root / "target/debug/muninn"), *args],
        input=json.dumps(request) if request is not None else None,
        text=True, capture_output=True, timeout=60,
    )
    with open(cli_log.name, "a") as log:
        log.write(result.stdout + result.stderr)
    assert result.returncode == 0, result.stderr
    result_json = json.loads(result.stdout)
    assert result_json["ok"], result_json
    return result_json["data"]

index_log = tempfile.NamedTemporaryFile(prefix="muninn-reconnect-index-", suffix=".log", dir="/tmp", delete=False)
mcp_log = tempfile.NamedTemporaryFile(prefix="muninn-reconnect-mcp-", suffix=".log", dir="/tmp", delete=False)
print(f"index log: {index_log.name}; MCP log: {mcp_log.name}; CLI log: {cli_log.name}", flush=True)
index = subprocess.Popen([str(root / "target/debug/muninn-index")], stdout=index_log, stderr=subprocess.STDOUT)
mcp = subprocess.Popen([str(root / "target/debug/muninn-mcp")], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=mcp_log, text=True, bufsize=1)
try:
    eventually(lambda: pids("muninn-index") and pids("muninn-index-listener") and pids("muninn-mcp"), "initial connections")
    repo = Path(target["fixture_root"]) / "reconnect-repository"
    repo.mkdir()
    (repo / "sample.txt").write_text("reconnectsentinel unique search content\n")
    initial = cli("preflight", str(repo), "--json")
    policy = initial["policy"]
    policy["embeddings"]["backend"] = "local"
    policy["embeddings"]["model"] = None
    policy["index"]["vendor"] = ["**"]
    cli("add", str(repo), "--json", "--input", "-", request={"api_version":1, "policy":policy})
    ready = cli("preflight", str(repo), "--json")
    cli("start", str(repo), "--json", "--input", "-", request={"api_version":1, "expected_family_id":ready["family_id"], "expected_revision":ready["revision"]})
    before = {name: pids(name) for name in ("muninn-index", "muninn-index-listener", "muninn-mcp")}
    sql("SELECT pg_terminate_backend(pid) FROM pg_stat_activity WHERE application_name IN ('muninn-index','muninn-index-listener','muninn-mcp')")
    for name, old in before.items():
        eventually(lambda: bool(pids(name) - old), name + " reconnection")
    assert index.poll() is None and mcp.poll() is None
    def search(query):
        request = {"jsonrpc":"2.0", "id":1, "method":"tools/call", "params":{"name":"search_fulltext", "arguments":{"repo":str(repo), "query":query}}}
        mcp.stdin.write(json.dumps(request) + "\n")
        mcp.stdin.flush()
        assert select.select([mcp.stdout], [], [], 20)[0], "MCP did not respond after reconnect"
        reply = json.loads(mcp.stdout.readline())
        assert reply["id"] == 1 and "error" not in reply, reply
        return query in json.dumps(reply).lower()
    assert search("reconnectsentinel")
    # Wait until the restarted watcher is attached before changing the file.
    eventually(lambda: bool(pids("muninn-index-watcher")), "watcher connection")
    time.sleep(1)
    (repo / "sample.txt").write_text("afterreconnectsentinel fresh content\n")
    eventually(lambda: search("afterreconnectsentinel"), "indexing after reconnect")
    # Deny new fixture connections and terminate existing ones. MCP must keep
    # its transport responsive and explain the outage, then recover.
    admin_sql("ALTER ROLE muninn_persistence_test NOLOGIN")
    try:
        admin_sql("SELECT pg_terminate_backend(pid) FROM pg_stat_activity WHERE usename='muninn_persistence_test'")
        time.sleep(1)
        request = {"jsonrpc":"2.0", "id":2, "method":"tools/call", "params":{"name":"search_fulltext", "arguments":{"repo":str(repo), "query":"afterreconnectsentinel"}}}
        mcp.stdin.write(json.dumps(request) + "\n")
        mcp.stdin.flush()
        assert select.select([mcp.stdout], [], [], 10)[0], "MCP did not respond during outage"
        reply = json.loads(mcp.stdout.readline())
        assert reply["id"] == 2 and "database" in reply["error"]["message"].lower(), reply
    finally:
        admin_sql("ALTER ROLE muninn_persistence_test LOGIN")
    eventually(lambda: bool(pids("muninn-mcp")), "MCP reconnect after outage")
    eventually(lambda: search("afterreconnectsentinel"), "MCP search after outage")
    print("Indexer, notification listener, and MCP reconnected; search and watcher indexing recovered")
finally:
    for process in (mcp, index):
        process.terminate()
        try:
            process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait()
    index_log.close()
    mcp_log.close()

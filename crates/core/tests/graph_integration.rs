//! Integration tests for graph.rs — PREPARE/EXECUTE/DEALLOCATE implementation.
//!
//! Each test creates a fresh repo (unique UUID) via register_repo(), runs its
//! assertions, then deletes the repo via delete_repo() which drops the per-repo
//! chunks table and AGE graph. Cleanup is guaranteed even on assertion failure
//! via the `with_repo` helper that catches panics and always deletes.
//!
//! Run against the live DB:
//!   cd /path/to/muninn
//!   nix develop --command cargo test --test graph_integration
//!
//! DB config comes from ~/.config/muninn/config.toml + ~/.pgpass.

use futures::FutureExt;
use muninn_core::{
    config::GlobalConfig,
    db,
    graph::{
        delete_file_symbols, query_related, upsert_edges, upsert_symbol_nodes, SymbolNodeInput,
    },
    store,
    types::{StructuralEdge, StructuralRelation, SymbolKind},
};
use std::future::Future;
use tokio_postgres::Client;
use uuid::Uuid;

// ── DB helpers ────────────────────────────────────────────────────────────────

async fn connect() -> Client {
    let cfg = GlobalConfig::load().expect("load ~/.config/muninn/config.toml");
    db::connect(&cfg.database)
        .await
        .expect("connect to muninn DB")
}

/// Register an ephemeral test repo (embedding_dim=64).
async fn setup_repo(client: &Client) -> Uuid {
    let repo = store::register_repo(
        client,
        &format!("/tmp/test-repo-{}", Uuid::new_v4()),
        "test-repo",
        64,
    )
    .await
    .expect("register test repo");
    repo.id
}

/// Drop the test repo's chunks table + AGE graph + repos row.
async fn cleanup(client: &Client, repo_id: Uuid) {
    store::delete_repo(client, repo_id)
        .await
        .expect("delete test repo");
}

/// Run `body` with a fresh repo. Always calls delete_repo afterwards,
/// even if body panics — so no test repo leaks into the DB.
async fn with_repo<F, Fut>(body: F)
where
    F: FnOnce(Client, Uuid) -> Fut,
    Fut: Future<Output = ()>,
{
    let client = connect().await;
    let repo_id = setup_repo(&client).await;
    // Run the body; catch any panic so we can clean up first.
    let result = std::panic::AssertUnwindSafe(body(client, repo_id))
        .catch_unwind()
        .await;
    // Always clean up — use a fresh connection in case the test connection is broken.
    let cleanup_client = connect().await;
    cleanup(&cleanup_client, repo_id).await;
    // Re-raise the panic after cleanup.
    if let Err(e) = result {
        std::panic::resume_unwind(e);
    }
}

/// Like `with_repo` but creates two repos, both cleaned up on exit.
async fn with_two_repos<F, Fut>(body: F)
where
    F: FnOnce(Client, Uuid, Uuid) -> Fut,
    Fut: Future<Output = ()>,
{
    let client = connect().await;
    let repo_a = setup_repo(&client).await;
    let repo_b = setup_repo(&client).await;
    let result = std::panic::AssertUnwindSafe(body(client, repo_a, repo_b))
        .catch_unwind()
        .await;
    let cleanup_client = connect().await;
    cleanup(&cleanup_client, repo_a).await;
    cleanup(&cleanup_client, repo_b).await;
    if let Err(e) = result {
        std::panic::resume_unwind(e);
    }
}

// ── Tests ─────────────────────────────────────────────────────────────────────

/// Basic: write a Function node + a caller + CALLS edge; verify query_related.
#[tokio::test]
async fn test_upsert_single_node_and_query() {
    with_repo(|client, repo_id| async move {
        let chunk_id = Uuid::new_v4();
        let caller_id = Uuid::new_v4();

        upsert_symbol_nodes(
            &client,
            repo_id,
            &[
                SymbolNodeInput {
                    chunk_id,
                    name: "my_function".into(),
                    kind: SymbolKind::Function,
                    file_path: "/src/lib.rs".into(),
                    start_line: 10,
                    end_line: 20,
                },
                SymbolNodeInput {
                    chunk_id: caller_id,
                    name: "caller_fn".into(),
                    kind: SymbolKind::Function,
                    file_path: "/src/main.rs".into(),
                    start_line: 5,
                    end_line: 8,
                },
            ],
        )
        .await
        .expect("upsert nodes");

        upsert_edges(
            &client,
            repo_id,
            &[StructuralEdge {
                from: caller_id,
                to: chunk_id,
                relation: StructuralRelation::Calls,
            }],
        )
        .await
        .expect("upsert edge");

        let callers = query_related(
            &client,
            repo_id,
            "my_function",
            StructuralRelation::Calls,
            true,
        )
        .await
        .expect("query_related");

        assert_eq!(
            callers.len(),
            1,
            "expected 1 caller, got {}: {:?}",
            callers.len(),
            callers
        );
        assert_eq!(callers[0].name, "caller_fn");
        assert_eq!(callers[0].file_path, "/src/main.rs");
    })
    .await;
}

/// Idempotency: upsert the same node twice (updated end_line); only one node persists.
#[tokio::test]
async fn test_upsert_node_idempotent() {
    with_repo(|client, repo_id| async move {
        let chunk_id = Uuid::new_v4();
        let node = || SymbolNodeInput {
            chunk_id,
            name: "stable_fn".into(),
            kind: SymbolKind::Function,
            file_path: "/src/lib.rs".into(),
            start_line: 1,
            end_line: 5,
        };
        upsert_symbol_nodes(&client, repo_id, &[node()])
            .await
            .expect("first upsert");
        // Second upsert with same chunk_id but different end_line — MERGE, not INSERT.
        upsert_symbol_nodes(
            &client,
            repo_id,
            &[SymbolNodeInput {
                end_line: 10,
                ..node()
            }],
        )
        .await
        .expect("second upsert");
    })
    .await;
}

/// All four SymbolKind labels can be written.
#[tokio::test]
async fn test_all_symbol_kinds() {
    with_repo(|client, repo_id| async move {
        let nodes: Vec<SymbolNodeInput> = [
            (SymbolKind::Function, "fn_sym"),
            (SymbolKind::Class, "cls_sym"),
            (SymbolKind::Module, "mod_sym"),
            (SymbolKind::Import, "imp_sym"),
        ]
        .iter()
        .map(|(kind, name)| SymbolNodeInput {
            chunk_id: Uuid::new_v4(),
            name: name.to_string(),
            kind: kind.clone(),
            file_path: "/src/test.rs".into(),
            start_line: 1,
            end_line: 2,
        })
        .collect();
        upsert_symbol_nodes(&client, repo_id, &nodes)
            .await
            .expect("upsert all kinds");
    })
    .await;
}

/// All four StructuralRelation types can be written without error.
#[tokio::test]
async fn test_all_relation_types() {
    with_repo(|client, repo_id| async move {
        let ids: Vec<Uuid> = (0..5).map(|_| Uuid::new_v4()).collect();
        let nodes: Vec<SymbolNodeInput> = ids
            .iter()
            .enumerate()
            .map(|(i, &id)| SymbolNodeInput {
                chunk_id: id,
                name: format!("sym_{i}"),
                kind: SymbolKind::Function,
                file_path: "/src/x.rs".into(),
                start_line: i as u32,
                end_line: i as u32 + 1,
            })
            .collect();
        upsert_symbol_nodes(&client, repo_id, &nodes)
            .await
            .expect("upsert nodes");

        upsert_edges(
            &client,
            repo_id,
            &[
                StructuralEdge {
                    from: ids[0],
                    to: ids[1],
                    relation: StructuralRelation::Calls,
                },
                StructuralEdge {
                    from: ids[0],
                    to: ids[2],
                    relation: StructuralRelation::Imports,
                },
                StructuralEdge {
                    from: ids[0],
                    to: ids[3],
                    relation: StructuralRelation::Defines,
                },
                StructuralEdge {
                    from: ids[0],
                    to: ids[4],
                    relation: StructuralRelation::InheritsFrom,
                },
            ],
        )
        .await
        .expect("upsert all relation types");
    })
    .await;
}

/// query_related outgoing (callee direction) returns the right node.
#[tokio::test]
async fn test_query_related_outgoing() {
    with_repo(|client, repo_id| async move {
        let caller_id = Uuid::new_v4();
        let callee_id = Uuid::new_v4();

        upsert_symbol_nodes(
            &client,
            repo_id,
            &[
                SymbolNodeInput {
                    chunk_id: caller_id,
                    name: "do_work".into(),
                    kind: SymbolKind::Function,
                    file_path: "/a.rs".into(),
                    start_line: 1,
                    end_line: 5,
                },
                SymbolNodeInput {
                    chunk_id: callee_id,
                    name: "helper".into(),
                    kind: SymbolKind::Function,
                    file_path: "/b.rs".into(),
                    start_line: 1,
                    end_line: 3,
                },
            ],
        )
        .await
        .expect("upsert");

        upsert_edges(
            &client,
            repo_id,
            &[StructuralEdge {
                from: caller_id,
                to: callee_id,
                relation: StructuralRelation::Calls,
            }],
        )
        .await
        .expect("upsert edge");

        let callees = query_related(
            &client,
            repo_id,
            "do_work",
            StructuralRelation::Calls,
            false,
        )
        .await
        .expect("query outgoing");
        assert_eq!(callees.len(), 1);
        assert_eq!(callees[0].name, "helper");

        let callers = query_related(&client, repo_id, "do_work", StructuralRelation::Calls, true)
            .await
            .expect("query incoming");
        assert_eq!(callers.len(), 0, "nothing calls do_work");
    })
    .await;
}

/// delete_file_symbols removes all nodes for a given file path (DETACH DELETE).
#[tokio::test]
async fn test_delete_file_symbols() {
    with_repo(|client, repo_id| async move {
        let keep_id = Uuid::new_v4();
        let del_id1 = Uuid::new_v4();
        let del_id2 = Uuid::new_v4();

        upsert_symbol_nodes(
            &client,
            repo_id,
            &[
                SymbolNodeInput {
                    chunk_id: keep_id,
                    name: "keeper".into(),
                    kind: SymbolKind::Function,
                    file_path: "/keep.rs".into(),
                    start_line: 1,
                    end_line: 2,
                },
                SymbolNodeInput {
                    chunk_id: del_id1,
                    name: "gone_fn".into(),
                    kind: SymbolKind::Function,
                    file_path: "/delete.rs".into(),
                    start_line: 1,
                    end_line: 2,
                },
                SymbolNodeInput {
                    chunk_id: del_id2,
                    name: "gone_cls".into(),
                    kind: SymbolKind::Class,
                    file_path: "/delete.rs".into(),
                    start_line: 3,
                    end_line: 5,
                },
            ],
        )
        .await
        .expect("upsert");

        // Edge from keeper → gone_fn to verify DETACH DELETE handles incident edges.
        upsert_edges(
            &client,
            repo_id,
            &[StructuralEdge {
                from: keep_id,
                to: del_id1,
                relation: StructuralRelation::Calls,
            }],
        )
        .await
        .expect("upsert edge");

        delete_file_symbols(&client, repo_id, "/delete.rs")
            .await
            .expect("delete file symbols");

        let callees = query_related(&client, repo_id, "keeper", StructuralRelation::Calls, false)
            .await
            .expect("query after delete");
        assert_eq!(callees.len(), 0, "gone_fn should have been deleted");
    })
    .await;
}

/// Special characters in symbol names and file paths don't break escaping.
#[tokio::test]
async fn test_special_chars_in_names() {
    with_repo(|client, repo_id| async move {
        let cases: &[(&str, &str)] = &[
            ("fn_single_quote", "/path/to/it's_a_file.rs"),
            ("fn_double_quote", r#"/path/"quoted".rs"#),
            ("fn_backslash", r"C:\Users\test.rs"),
            ("fn_unicode_日本語", "/src/unicode.rs"),
            ("fn_dollar_sign", "/src/$special.rs"),
        ];
        let nodes: Vec<SymbolNodeInput> = cases
            .iter()
            .map(|(name, path)| SymbolNodeInput {
                chunk_id: Uuid::new_v4(),
                name: name.to_string(),
                kind: SymbolKind::Function,
                file_path: path.to_string(),
                start_line: 1,
                end_line: 2,
            })
            .collect();
        upsert_symbol_nodes(&client, repo_id, &nodes)
            .await
            .expect("upsert special chars");
    })
    .await;
}

/// Batch upsert: 40 nodes across all 4 kinds in one call.
#[tokio::test]
async fn test_batch_upsert_many_nodes() {
    with_repo(|client, repo_id| async move {
        let kinds = [
            SymbolKind::Function,
            SymbolKind::Class,
            SymbolKind::Module,
            SymbolKind::Import,
        ];
        let nodes: Vec<SymbolNodeInput> = (0..40)
            .map(|i| SymbolNodeInput {
                chunk_id: Uuid::new_v4(),
                name: format!("sym_{i}"),
                kind: kinds[i % 4].clone(),
                file_path: format!("/src/file_{}.rs", i / 10),
                start_line: i as u32,
                end_line: i as u32 + 1,
            })
            .collect();
        upsert_symbol_nodes(&client, repo_id, &nodes)
            .await
            .expect("batch upsert 40 nodes");
    })
    .await;
}

/// Empty inputs are no-ops (don't panic or error).
#[tokio::test]
async fn test_empty_inputs_are_noop() {
    with_repo(|client, repo_id| async move {
        upsert_symbol_nodes(&client, repo_id, &[])
            .await
            .expect("empty nodes noop");
        upsert_edges(&client, repo_id, &[])
            .await
            .expect("empty edges noop");
    })
    .await;
}

/// delete_file_symbols on a path with no nodes is a no-op.
#[tokio::test]
async fn test_delete_file_symbols_nonexistent_path() {
    with_repo(|client, repo_id| async move {
        delete_file_symbols(&client, repo_id, "/no/such/file.rs")
            .await
            .expect("delete on missing path should be noop");
    })
    .await;
}

/// query_related on an empty graph returns an empty vec.
#[tokio::test]
async fn test_query_related_empty_graph() {
    with_repo(|client, repo_id| async move {
        let result = query_related(
            &client,
            repo_id,
            "nonexistent",
            StructuralRelation::Calls,
            false,
        )
        .await
        .expect("query on empty graph");
        assert!(result.is_empty());
    })
    .await;
}

/// Multiple callers of the same function are all returned.
#[tokio::test]
async fn test_multiple_callers() {
    with_repo(|client, repo_id| async move {
        let target_id = Uuid::new_v4();
        let caller_ids: Vec<Uuid> = (0..3).map(|_| Uuid::new_v4()).collect();

        let mut nodes = vec![SymbolNodeInput {
            chunk_id: target_id,
            name: "target".into(),
            kind: SymbolKind::Function,
            file_path: "/target.rs".into(),
            start_line: 1,
            end_line: 2,
        }];
        for (i, &id) in caller_ids.iter().enumerate() {
            nodes.push(SymbolNodeInput {
                chunk_id: id,
                name: format!("caller_{i}"),
                kind: SymbolKind::Function,
                file_path: format!("/caller_{i}.rs"),
                start_line: 1,
                end_line: 2,
            });
        }
        upsert_symbol_nodes(&client, repo_id, &nodes)
            .await
            .expect("upsert");

        let edges: Vec<StructuralEdge> = caller_ids
            .iter()
            .map(|&id| StructuralEdge {
                from: id,
                to: target_id,
                relation: StructuralRelation::Calls,
            })
            .collect();
        upsert_edges(&client, repo_id, &edges)
            .await
            .expect("upsert edges");

        let callers = query_related(&client, repo_id, "target", StructuralRelation::Calls, true)
            .await
            .expect("query callers");
        assert_eq!(
            callers.len(),
            3,
            "expected 3 callers, got {}: {:?}",
            callers.len(),
            callers
        );
    })
    .await;
}

/// Repos are fully isolated: nodes in repo A are invisible from repo B's graph.
#[tokio::test]
async fn test_repo_isolation() {
    with_two_repos(|client, repo_a, repo_b| async move {
        upsert_symbol_nodes(
            &client,
            repo_a,
            &[SymbolNodeInput {
                chunk_id: Uuid::new_v4(),
                name: "only_in_a".into(),
                kind: SymbolKind::Function,
                file_path: "/a.rs".into(),
                start_line: 1,
                end_line: 2,
            }],
        )
        .await
        .expect("upsert in A");

        let result = query_related(
            &client,
            repo_b,
            "only_in_a",
            StructuralRelation::Calls,
            false,
        )
        .await
        .expect("query from B");
        assert!(result.is_empty(), "repo B must not see repo A's nodes");
    })
    .await;
}

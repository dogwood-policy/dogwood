// dogwood-lsp handles Unix paths and file URIs only, so its tests run on Unix.
#![cfg(unix)]

#[path = "support/dogwood_cli.rs"]
pub mod dogwood_cli;
#[path = "support/dogwood_cli_self_tests.rs"]
mod dogwood_cli_self_tests;
#[path = "support/lsp_process.rs"]
pub mod lsp_process;
#[path = "support/lsp_process_self_tests.rs"]
mod lsp_process_self_tests;

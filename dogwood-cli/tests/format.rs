use std::io::Write;
use std::process::{Command, Stdio};

#[test]
fn format_command_reads_stdin_and_writes_pretty_policy() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_dogwood"))
        .args(["format", "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("spawn dogwood");

    child
        .stdin
        .take()
        .expect("piped stdin")
        .write_all(b"permit (principal, action, resource) when { true };")
        .expect("write policy");

    let output = child.wait_with_output().expect("wait for dogwood");
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8(output.stdout).expect("utf-8 output"),
        "permit (principal, action, resource)\nwhen { true };\n"
    );
}

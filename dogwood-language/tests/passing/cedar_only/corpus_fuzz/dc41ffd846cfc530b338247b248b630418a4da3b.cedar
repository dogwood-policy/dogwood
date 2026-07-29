permit(
  principal in a::"ff\u{e}",
  action == Action::"action",
  resource
) when {
  true && ((a::"ff\u{e}".getTag("f")) has ffff)
};

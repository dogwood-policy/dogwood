@d("")
@x("")
forbid(
  principal in a::"r@",
  action in [Action::"action"],
  resource is a in a::"r@"
) when {
  true
};

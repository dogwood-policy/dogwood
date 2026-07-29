forbid(
  principal == a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource
) when {
  true && ((ip("54.54.54.101/0")).isInRange(ip("0.0.0.0")))
};

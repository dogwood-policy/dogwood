forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && ((ip("::300:0:0")) == (decimal("0.0")))
};

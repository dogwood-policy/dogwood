forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && ((ip(".0.0.0")) == (decimal("0.0")))
};

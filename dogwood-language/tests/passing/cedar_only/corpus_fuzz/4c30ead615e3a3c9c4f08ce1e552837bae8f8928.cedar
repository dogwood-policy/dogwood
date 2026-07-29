permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && ((ip("::2d:0:2d2d")).isInRange(ip("0.0.0.0")))
};

permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && ((ip("")).isMulticast(ip("::2d:2d2d"), ip("0.0.0.0")))
};

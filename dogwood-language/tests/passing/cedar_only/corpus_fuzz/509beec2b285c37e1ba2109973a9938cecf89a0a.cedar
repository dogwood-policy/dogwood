permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && ((ip("::2d2d:3a2d:2d07")).isIpv4())
};

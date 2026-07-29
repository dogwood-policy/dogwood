permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (if ((ip("")).isIpv4()) then ((ip("::2d2d:2d2d:2d7d")).isMulticast()) else false)) && false) && false
};

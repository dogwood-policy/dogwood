permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (if ((ip("::2d:2d2d:3a2d")).isIpv4()) then false else false)) && false) && false
};

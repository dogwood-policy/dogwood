permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (if ((ip("::4000:2d2d:2d3a:2d2d")).isIpv4()) then false else false)) && false) && false
};

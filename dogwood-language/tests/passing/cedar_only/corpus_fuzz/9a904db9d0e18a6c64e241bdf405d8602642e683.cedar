permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && ((ip("45.45.45.45/0")).isIpv4())) && false) && false
};

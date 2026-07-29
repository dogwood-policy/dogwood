forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && ((if ((ip("::ff")).isIpv6()) then (ip("0.0.0.0")) else (ip("0.0.0.0"))).isIpv6())) && false) && false
};

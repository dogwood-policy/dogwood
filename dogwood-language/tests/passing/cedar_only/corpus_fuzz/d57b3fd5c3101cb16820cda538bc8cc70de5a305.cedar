forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && ((if false then (ip("33.105.98.101/24")) else (ip("0.0.0.0"))).isIpv4())) && false) && false
};

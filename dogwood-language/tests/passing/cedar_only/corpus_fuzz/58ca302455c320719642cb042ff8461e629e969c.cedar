forbid(
  principal == a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource
) when {
  ((true && ((if false then (if false then (ip("0.0.0.0")) else (ip("0.0.0.32"))) else (ip("\0 "))).isIpv6())) && ((if false then (if false then (ip("0.00.0")) else (ip("0.0.0.0"))) else (ip("0.0.0.0"))).isInRange(ip("0.0.0.0")))) && false
};

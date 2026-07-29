forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  ((true && (((if false then (ip("189.189.19.0/24")) else (ip("0.0.0.0"))).isIpv4()) && false)) && false) && false
};

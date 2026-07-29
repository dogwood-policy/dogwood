permit(
  principal,
  action in [Action::"action"],
  resource == a::"\u{2}"
) when {
  true && (!((if false then (ip("0.0.0.0")) else (ip("0.0.0.4"))).isIpv4()))
};

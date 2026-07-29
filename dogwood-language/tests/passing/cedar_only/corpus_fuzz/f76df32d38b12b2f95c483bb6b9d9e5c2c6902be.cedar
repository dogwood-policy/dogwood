permit(
  principal,
  action in [Action::"action"],
  resource == a::"@\u{e}"
) when {
  true && (!((if false then (ip("0.0.0.0")) else (ip("253.52.119.67"))).isIpv4()))
};

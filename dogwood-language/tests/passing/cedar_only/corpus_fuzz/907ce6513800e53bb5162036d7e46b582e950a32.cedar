permit(
  principal,
  action in [Action::"action"],
  resource == a::"@"
) when {
  true && (!((if false then (ip("0.0.0.0")) else (ip("ffff:ffff:ffff:ffff:ffff:fffff:ffff:ffff/126"))).isMulticast()))
};

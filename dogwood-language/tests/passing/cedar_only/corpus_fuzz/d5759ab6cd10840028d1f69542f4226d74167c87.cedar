permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  true && (!((if false then (ip("::ffff:55b0:b0b0:b0b0:b0b0:6544")) else (ip("ffff:ffff:ffff:ffff:ffff:fffff:ffff:ffff/126"))).isMulticast()))
};

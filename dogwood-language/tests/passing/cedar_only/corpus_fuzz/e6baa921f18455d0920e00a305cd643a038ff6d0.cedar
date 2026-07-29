permit(
  principal,
  action in [Action::"action"],
  resource == a::"@"
) when {
  true && (!((if false then (ip("ff00:0:ff:55b0:b0b0:b0b0:b0b0:6544")) else (ip("::ffff:55.2555.255.255"))).isMulticast()))
};

permit(
  principal,
  action in [Action::"action"],
  resource == a::"\u{e}\0\0\0"
) when {
  true && (!((if true then (ip("68.79.34.105/11")) else (ip("176.176.0.0"))).isMulticast()))
};

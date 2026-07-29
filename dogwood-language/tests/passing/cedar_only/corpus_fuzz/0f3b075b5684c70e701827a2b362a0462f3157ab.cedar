permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  true && (!((if true then (ip("b0b0:b0b0:b0b0:b065:444f:9400:6e6:6974/Y26")) else (ip("0.0.0.0"))).isMulticast()))
};

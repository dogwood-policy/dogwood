@UAAAAA("III")
permit(
  principal,
  action in [Action::"action"],
  resource == a::"@"
) when {
  true && (!((if true then (ip("ffff:b0b0:b0b0:b065:444f:9400:6e6f:6974/1Y6")) else (ip("::"))).isMulticast()))
};

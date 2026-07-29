@UAAAAA("IIIII")
permit(
  principal,
  action in [Action::"action"],
  resource == a::"@"
) when {
  true && (!((if false then (ip("b0b0:b0cc:b0b0:b0b0:b020:6e61:6962:6544")) else (ip("0.0.0.0"))).isMulticast()))
};

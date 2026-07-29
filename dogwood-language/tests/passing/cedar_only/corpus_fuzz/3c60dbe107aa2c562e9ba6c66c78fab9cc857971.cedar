@UAAAAA("II")
permit(
  principal,
  action in [Action::"action"],
  resource == a::"@"
) when {
  true && (!((if false then (ip("::3aff:55b0:b0b0:b0b0:b0b06544/114")) else (ip("5.51.51.51/188"))).isMulticast()))
};

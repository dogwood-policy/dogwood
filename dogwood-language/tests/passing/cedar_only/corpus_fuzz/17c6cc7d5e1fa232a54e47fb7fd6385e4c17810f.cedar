@UAAAAA("I")
permit(
  principal,
  action in [Action::"action"],
  resource == a::"@"
) when {
  true && (!((if false then (ip("::3aff:55b0:b0b0:b0b0:b0b:6544//1")) else (ip("51.51.51.51/116"))).isMulticast()))
};

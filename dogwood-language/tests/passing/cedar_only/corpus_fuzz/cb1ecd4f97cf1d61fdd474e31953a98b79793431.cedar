@A00000000("")
@B5("bi")
permit(
  principal,
  action in [Action::"action"],
  resource == a::"33"
) when {
  true
};

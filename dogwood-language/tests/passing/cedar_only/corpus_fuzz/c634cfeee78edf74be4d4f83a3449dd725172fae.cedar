@A00000000("")
@B5("bi")
permit(
  principal is a in a::"33",
  action in [Action::"action"],
  resource == a::"33"
) when {
  true
};

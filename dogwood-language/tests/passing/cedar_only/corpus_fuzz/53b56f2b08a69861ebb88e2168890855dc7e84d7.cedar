permit(
  principal == a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  true && ((ip("::72:ff9:f9f9:ffff")).isMulticast())
};

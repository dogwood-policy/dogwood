permit(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  (true && ((a::"\n\0\0\0" in a::"\n\0\0\0") || false)) && false
};

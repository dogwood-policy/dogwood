permit(
  principal == a::"",
  action in [Action::"action"],
  resource in a::"\0"
) when {
  true
};

permit(
  principal is a in a::"\0",
  action in [Action::"action"],
  resource == a::"\0"
) when {
  false
};

permit(
  principal is a,
  action in [Action::"action"],
  resource == a::"\0"
) when {
  true
};

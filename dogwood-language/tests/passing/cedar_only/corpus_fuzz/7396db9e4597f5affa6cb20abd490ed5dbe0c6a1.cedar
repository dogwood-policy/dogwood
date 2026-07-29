permit(
  principal is a,
  action in [Action::"action"],
  resource == a::""
) when {
  (true && ([].isEmpty())) && true
};

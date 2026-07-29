permit(
  principal is a,
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (resource.r)) && (a::"".r)
};

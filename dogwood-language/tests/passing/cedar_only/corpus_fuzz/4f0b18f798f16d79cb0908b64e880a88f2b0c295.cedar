forbid(
  principal is a in a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource is a in a::""
) when {
  ((true && ([].contains(context))) && (principal has r)) && (principal has r)
};

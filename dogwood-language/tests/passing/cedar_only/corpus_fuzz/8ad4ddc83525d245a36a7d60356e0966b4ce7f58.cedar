forbid(
  principal is a in a::"\0\0\0\0\0\0\0\0\0<\0\0\0\0\0\0\0",
  action in [Action::"action",Action::"action",Action::"action"],
  resource == a::"\0\0\0\0\0\0\0\0\0<\0\0\0\0\0\0\0"
) when {
  true
};

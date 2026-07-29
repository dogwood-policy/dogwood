forbid(
  principal in r::"\0\0\0",
  action in [Action::"action",Action::"action",Action::"action"],
  resource == r::"\0\0\0"
) when {
  (true && (r::"\0\0\0" is r)) && ([].contains(N::"\0"))
};

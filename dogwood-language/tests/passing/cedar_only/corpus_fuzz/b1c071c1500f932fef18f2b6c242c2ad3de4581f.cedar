forbid(
  principal,
  action in [Action::"action"],
  resource == a::"\0\0\03"
) when {
  true && ([].contains(context))
};

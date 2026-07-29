forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && ((a::"".getTag(principal.getTag("\0\0\0\0V"))) like "VA")
};

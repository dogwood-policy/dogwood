forbid(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  true && ((a::"".getTag(principal.getTag("\0\0\0\u{4}\u{1d}"))) like "\0V")
};

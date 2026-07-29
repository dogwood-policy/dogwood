forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && ((a::"\u{4}\0\0".getTag(principal.getTag("\0\0\0\u{4}\u{1d}\0\0VVV\0\0\0TTTT\0\0\0\0\0\0\0\0TTTTTTTTT"))) like "")
};

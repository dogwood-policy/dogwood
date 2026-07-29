forbid(
  principal == a::"\0\0\0\0\0\0\0\0\0-\0\0\0\0\u{1}\0\0\0\0\0\0\u{4}\0\0",
  action in [Action::"action"],
  resource is a in a::"\0\0\0\0\0\0\0\0\0-\0\0\0\0\u{1}\0\0\0\0\0\0\u{4}\0\0"
) when {
  true
};

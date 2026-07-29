@B1("\u{1}\u{1}\u{1}\u{1}n \0\0\0\0e")
forbid(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  (false && (principal has A)) && true
};

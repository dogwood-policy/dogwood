forbid(
  principal is a,
  action in [Action::"action"],
  resource in a::""
) when {
  (true && (({"\u{7}\0\0\0": []}["\u{7}\0\0\0"]).containsAny([]))) && false
};

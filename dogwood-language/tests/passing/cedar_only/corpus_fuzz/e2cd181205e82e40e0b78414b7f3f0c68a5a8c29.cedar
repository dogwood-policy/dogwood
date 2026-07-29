forbid(
  principal is a,
  action in [Action::"action"],
  resource in a::""
) when {
  (true && ([[[], []], [[], [], []]].containsAny([]))) && false
};

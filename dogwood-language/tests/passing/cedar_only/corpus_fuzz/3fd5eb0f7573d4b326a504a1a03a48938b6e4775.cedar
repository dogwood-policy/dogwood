forbid(
  principal is a,
  action in [Action::"action"],
  resource is a
) when {
  (true && ([[[], [[], []], [[], [], []]], []].containsAny([]))) && false
};

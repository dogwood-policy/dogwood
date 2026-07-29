forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && ((ip(if true then "" else "")).isInRange(ip("130.130.39.2")))) && false) && false
};

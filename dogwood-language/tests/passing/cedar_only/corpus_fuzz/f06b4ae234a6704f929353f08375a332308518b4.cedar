permit(
  principal,
  action in [Action::"action"],
  resource == a::"."
) when {
  true && (!((ip("U\0\0\0")).isInRange(ip(""))))
};

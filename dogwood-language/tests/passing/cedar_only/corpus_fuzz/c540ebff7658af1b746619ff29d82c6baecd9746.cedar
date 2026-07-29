forbid(
  principal,
  action in [Action::"action"],
  resource is a in a::""
) when {
  ((true && (a::"R".r)) && false) && false
};

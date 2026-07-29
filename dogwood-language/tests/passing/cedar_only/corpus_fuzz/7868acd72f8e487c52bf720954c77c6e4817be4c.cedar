forbid(
  principal,
  action in [Action::"action"],
  resource is a in a::""
) when {
  true && (((duration("7424ms")).toHours()) == (ip("0.0.0.0")))
};

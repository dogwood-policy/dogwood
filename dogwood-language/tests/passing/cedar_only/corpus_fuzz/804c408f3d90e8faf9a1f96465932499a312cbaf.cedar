@r("")
forbid(
  principal,
  action in [Action::"action"],
  resource is a in a::""
) when {
  ((true && (principal in principal)) && true) && true
};

forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && ((if (action in [principal, a::""]) then 15 else 0) == 0)) && false) && false
};

permit(
  principal,
  action in [Action::"action"],
  resource in a::""
) when {
  true && ((if ([action].isEmpty()) then (if true then [principal] else [action, principal, a::""]) else []).isEmpty())
};

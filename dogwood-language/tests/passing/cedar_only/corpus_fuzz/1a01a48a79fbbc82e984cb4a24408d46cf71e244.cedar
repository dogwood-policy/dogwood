forbid(
  principal in a::"",
  action in [Action::"action"],
  resource in a::""
) when {
  true && ((if ([action].isEmpty()) then (if true then [action] else [action]) else (if true then [a::"", action, principal] else [a::""])).isEmpty())
};

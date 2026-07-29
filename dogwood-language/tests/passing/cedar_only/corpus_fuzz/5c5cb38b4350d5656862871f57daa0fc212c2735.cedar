@A0000000("")
forbid(
  principal in a::"",
  action == Action::"action",
  resource == a::""
) when {
  (true && ((if ([action].isEmpty()) then (if true then [action] else [action]) else (if true then [action] else [action])).isEmpty())) && ((if ([action].isEmpty()) then [action] else [action]).isEmpty())
};

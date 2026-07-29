@y00000000("")
forbid(
  principal == a::"",
  action,
  resource == a::""
) when {
  (true && ((if ([action].isEmpty()) then (if true then [action] else [action]) else (if true then [] else [action])).isEmpty())) && ((if ([action].isEmpty()) then [action] else [resource, a::""]).isEmpty())
};

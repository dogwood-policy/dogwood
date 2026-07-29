forbid(
  principal in a::"\0\0\0",
  action in [Action::"action",Action::"action"],
  resource in a::"\0\0\0"
) when {
  (true && ((if ("" like "") then (if true then [[[[a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [principal], [a::"\0\0\0", principal, action]], [[a::"\0\0\0", action, action], [action], [action]], [[action]]], [[[action]]], [[[a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"]]]] else [[[[a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [action], [a::"\0\0\0"]], [[action, action, action], [action, action, a::"\0\0\0"], [action, action, action]], [[a::"\0\0\0", resource, a::"\0\0\0"], [a::"\0\0\0", action, action], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"]]], [[[action], [action], [a::"\0\0\0", action, action]], [], [[principal, a::"\0\0\0", a::"\0\0\0"], [principal, action, resource], [action]]], [[], [[a::"\0\0\0", action, action]]]]) else [[[[a::"\0\0\0", action, action], [principal], [a::"\0\0\0", action, action]]], [[[a::"\0\0\0"], [action, action, principal], []], [[], [], []], []], []]).containsAny([]))) && false
};

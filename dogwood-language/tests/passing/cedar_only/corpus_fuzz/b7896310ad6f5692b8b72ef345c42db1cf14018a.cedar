forbid(
  principal in a::"\0\0\0",
  action in [Action::"action",Action::"action"],
  resource in a::"\0\0\0"
) when {
  (true && ((if ("" like "") then (if true then [[[[a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", principal], []], [[a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", principal, a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"]], [[a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"]]], [[[a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"]], [[a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", principal, resource]], [[action, resource, resource], [resource, resource]]], [[[resource, a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"]], []]] else [[[[principal], [resource, resource], [resource, resource]], [[resource, resource], [resource, resource]]], [[[resource, resource], [resource, principal]], [[resource, resource], [resource, resource]]]]) else (if false then [[[[resource, resource], [resource, resource]]], [[[action, principal], [], []], []]] else [])).containsAny([]))) && false
};

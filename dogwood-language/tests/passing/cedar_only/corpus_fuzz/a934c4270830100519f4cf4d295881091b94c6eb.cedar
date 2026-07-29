forbid(
  principal in a::"\0\0\0",
  action in [Action::"action",Action::"action"],
  resource in a::"\0\0\0"
) when {
  (true && ((if ("" like "") then (if true then [[[[a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"]], [[resource, resource, resource], [resource, resource], [action, principal, resource]], [[resource, resource], [resource, resource]]], [[[resource, resource], [resource, resource]], [[resource, resource], []]], [[], []]] else []) else []).containsAny(if ("" like "") then (if false then [[[[resource, resource], []], [[resource, resource], [resource, resource]]], [[[a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", resource]], [[], [], []], [[a::"\0\0\0"]]]] else [[[[a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"]], [[resource, a::"\0\0\0", a::"\0\0\0"], [], []], [[a::"\0\0\0", resource], [resource]]], [[[action, principal, principal], [], []], [[resource, resource], []]], [[[principal], [resource, resource, a::"\0\0\0"], []], [[]], [[], []]]]) else [[[[resource, principal], []], []], []]))) && false
};

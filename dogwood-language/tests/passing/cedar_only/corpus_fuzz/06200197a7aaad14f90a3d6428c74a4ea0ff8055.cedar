forbid(
  principal in a::"\0\0\0",
  action in [Action::"action",Action::"action"],
  resource in a::"\0\0\0"
) when {
  (true && ((if ("" like "") then (if true then [[[[a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"]], [[resource, resource, resource], [resource, resource], [action, principal, action]], [[resource, resource], [resource, resource]]], [[[resource, resource], [resource, resource]], [[resource, resource], []]], [[], []]] else []) else []).containsAny(if ("" like "") then (if false then [[[[resource, resource], []], [[resource, resource], [resource, resource]]], [[[a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", resource]], [[], [], []], [[a::"\0\0\0"]]]] else [[[[a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [principal]], [], []], [], [[[resource, principal], [a::"\0\0\0", principal, a::"\0\0\0"]], [[principal, principal], [principal]]]]) else [[], []]))) && false
};

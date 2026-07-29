forbid(
  principal in a::"\0\0\0",
  action in [Action::"action",Action::"action"],
  resource in a::"\0\0\0"
) when {
  (true && ((if ("" like "") then (if true then [[[[a::"\0\0\0", a::"\0\0\0", resource], [resource, resource], [resource, resource]], [[resource, resource], [principal]], [[principal, a::"\0\0\0"], [], [resource, resource]]], [[], [], []], [[[a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"]]]] else [[[[a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [], []], [[], [principal, action, action]], [[a::"\0\0\0", resource], []]], [], []]) else [[[[a::"\0\0\0", a::"\0\0\0"], [principal, a::"\0\0\0"]], [[]]], [[[resource, principal], []], [[]], [[], []]]]).containsAny(if false then [[[[], [datetime("5672-01-01"), datetime("0000-01-01")]]]] else []))) && false
};

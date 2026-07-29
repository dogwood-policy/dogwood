forbid(
  principal in a::"\0\0\0",
  action in [Action::"action",Action::"action"],
  resource in a::"\0\0\0"
) when {
  (true && ((if ("" like "") then (if true then [[[[a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", principal], []], [[a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", action, a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", resource]], []], [], [[[a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [principal, principal, a::"\0\0\0"], [a::"\0\0\0", resource, resource]], [[resource, resource], [principal, resource]], [[a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", resource, resource]]]] else [[[[principal, resource], [resource, resource]], [[resource, resource], []]], [[]]]) else (if true then [[[[resource, resource], [resource, resource], [resource, resource]]]] else [[[[resource, resource], [resource, principal]], [[resource, resource], [resource, resource]]], [[], [[resource, resource], [resource, resource]]]])).containsAny([[[[ip("::6962"), ip("0.0.0.0"), ip("0.0.0.0")], [], []], [], []], [], []]))) && false
};

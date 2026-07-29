forbid(
  principal in a::"\0\0\0",
  action in [Action::"action",Action::"action"],
  resource in a::"\0\0\0"
) when {
  (true && ((if ("" like "") then (if false then [[[[principal, a::"\0\0\0"], [resource, resource]], [[resource, a::"\0\0\0"], [resource, resource]]], [[[resource, resource], [resource, resource]], []]] else [[[[resource, resource], [resource, resource]], [[resource, resource], [resource, resource]]], [[[principal, action], [action, principal]], []]]) else []).containsAny([]))) && false
};

forbid(
  principal in a::"\0\0\0",
  action in [Action::"action",Action::"action"],
  resource in a::"\0\0\0"
) when {
  (true && ((if ("" like "") then (if false then [[[[resource, a::"\0\0\0"], [resource, resource]], [[resource, resource], [resource, resource]]], [[[resource, resource], [resource, resource]], [[resource, principal], [resource, resource]]]] else [[[[resource, resource], [resource, resource]], [[action, resource, resource], [resource, resource]]], [[[resource, resource], [action, resource]], [[], [resource]]]]) else [[[]]]).containsAny([]))) && false
};

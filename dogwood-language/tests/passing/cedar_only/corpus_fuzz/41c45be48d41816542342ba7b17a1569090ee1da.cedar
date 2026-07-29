permit(
  principal == a::"\0\0\0",
  action,
  resource in a::"\0\0\0"
) when {
  (true && ((if ("" like "") then (if true then [[[[a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"]], [[resource, resource, resource], [resource, resource], [action, principal, resource]], [[resource, resource], [resource, resource]]], [[[resource, resource], [resource, resource]], [[resource, resource], []]], [[[resource, resource], [resource, resource]], [[resource, resource], [a::"\0\0\0", resource]]]] else [[], []]) else []).containsAny([]))) && false
};

forbid(
  principal in a::"\0\0\0",
  action in [Action::"action",Action::"action"],
  resource in a::"\0\0\0"
) when {
  (true && ((if ("" like "") then (if true then [[[[a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", resource, resource], [resource, resource]], [[principal, resource], [resource, resource]], [[a::"\0\0\0", a::"\0\0\0"], [principal, principal, principal]]], [], []] else []) else []).containsAny([]))) && false
};

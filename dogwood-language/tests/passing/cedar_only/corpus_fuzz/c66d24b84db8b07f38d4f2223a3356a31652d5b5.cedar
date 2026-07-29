forbid(
  principal in a::"\0",
  action in [Action::"action",Action::"action"],
  resource in a::"\0"
) when {
  (true && ((if ("" like "") then (if false then [[[[], [principal], []], [[resource]]], [[[action, resource], [a::"\0"], [a::"\0", principal, action]], [[principal, action], [action, action]]]] else [[[[], [], [resource, resource]], [[action, principal, a::"\0"], [action, action, resource]], [[action, principal, a::"\0"], [action, a::"\0", principal]]], [], []]) else []).containsAny([]))) && false
};

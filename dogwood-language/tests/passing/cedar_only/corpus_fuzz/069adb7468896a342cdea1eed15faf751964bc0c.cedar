permit(
  principal,
  action,
  resource in a::""
) when {
  (true && ((if ("" like "") then (if true then [[[[resource, a::""], [action], [action]], [[action]], [[resource, resource, resource]]], [[[]], [[], [], [a::"", resource, a::""]]], [[[a::"", a::""], [principal, principal, principal], [principal]], [[resource, action], [], [a::"", a::"", a::""]], [[a::"", a::"", a::""], [a::"", action, action], [resource, resource, resource]]]] else [[[]], []]) else [[[[action, principal], [a::"", principal, a::""]], [[], [], []], [[resource, resource], [resource, resource]]], [[[action], [a::""]], [[resource, action], []]]]).containsAny([]))) && ((if false then [datetime("9578-11-31T10:34:34.000Z"), datetime("0000-01-01")] else []).isEmpty())
};

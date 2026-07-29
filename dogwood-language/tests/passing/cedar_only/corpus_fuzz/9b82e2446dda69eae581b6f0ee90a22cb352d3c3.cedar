forbid(
  principal in a::"\0\0\0",
  action in [Action::"action",Action::"action"],
  resource in a::"\0\0\0"
) when {
  (true && ((if ("" like "") then (if true then [[[[a::"\0\0\0", a::"\0\0\0", action], [action], [a::"\0\0\0"]], [[action, action, action], [action, action, action], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"]], [[action, action, action], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [action, action, action]]], [[[a::"\0\0\0", action, action], [a::"\0\0\0", action, principal], []]], [[], [], []]] else []) else []).containsAny([]))) && false
};

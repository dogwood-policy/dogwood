forbid(
  principal in a::"\0\0\0",
  action in [Action::"action",Action::"action"],
  resource in a::"\0\0\0"
) when {
  (true && ((if ("y\0" like "") then (if true then [[[], [], []], [], []] else []) else ({"                           ": [[[[resource, resource, action], [principal, principal], []], [], []]]}["                           "])).containsAny([]))) && false
};

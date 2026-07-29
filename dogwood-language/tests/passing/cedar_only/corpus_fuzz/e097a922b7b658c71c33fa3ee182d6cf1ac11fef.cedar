forbid(
  principal in a::"\0\0\0",
  action in [Action::"action",Action::"action"],
  resource in a::"\0\0\0"
) when {
  (true && ((if ("" like "") then (if true then [] else [[[[a::"\0\0\0", principal, a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", principal]], [[a::"\0\0\0", a::"\0\0\0"], [a::"\0\0\0", a::"\0\0\0", a::"\0\0\0"]], [[], [resource, a::"\0\0\0"], []]], [[[resource, action], []], []], []]) else []).containsAny([(ip("254.254.254.254")).isLoopback(), (ip("254.254.254.254/0")).isLoopback()]))) && ("" like "")
};

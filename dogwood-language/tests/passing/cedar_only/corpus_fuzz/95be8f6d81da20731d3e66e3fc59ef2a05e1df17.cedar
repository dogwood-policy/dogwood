forbid(
  principal in a::"\0\0",
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::"\0\0"
) when {
  (true && ({"": "" like ""}[""])) && ((if ("" like "") then [] else []).containsAny(if ("" like "") then (if false then [[[], []], []] else [[[[resource, resource], [principal, principal], [resource, principal]], [], []], []]) else []))
};

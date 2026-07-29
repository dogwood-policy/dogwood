forbid(
  principal is a,
  action in [Action::"action",Action::"action"],
  resource in a::"\0\0\0"
) when {
  true && ((if ([[resource, resource], [a::"\0\0\0", a::"\0\0\0"]].containsAny([[principal, principal, principal], [], []])) then [] else []).containsAny([]))
};

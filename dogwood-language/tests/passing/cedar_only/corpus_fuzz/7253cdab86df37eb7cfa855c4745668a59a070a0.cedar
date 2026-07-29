forbid(
  principal is a,
  action in [Action::"action",Action::"action"],
  resource in a::"\0\0\0"
) when {
  true && ((if ([[principal, action], [action, action]].containsAny([])) then [{"": ""}, {"": ""}] else [context, context, context]).containsAny([]))
};

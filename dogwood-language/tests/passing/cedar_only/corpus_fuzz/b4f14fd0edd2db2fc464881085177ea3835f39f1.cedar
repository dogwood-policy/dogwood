permit(
  principal is a,
  action in [Action::"action",Action::"action",Action::"action"],
  resource == a::"\0"
) when {
  ((true && (action in [action, action, action])) && (action in [action, action, action])) && (action in [a::"\0", a::"\0", principal])
};

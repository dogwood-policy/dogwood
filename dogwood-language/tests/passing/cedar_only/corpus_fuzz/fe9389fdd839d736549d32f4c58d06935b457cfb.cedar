forbid(
  principal == a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource == a::""
) when {
  ((true && (action in [action, action, action])) && (action in [action, action, action])) && (action in [action, a::"", a::""])
};

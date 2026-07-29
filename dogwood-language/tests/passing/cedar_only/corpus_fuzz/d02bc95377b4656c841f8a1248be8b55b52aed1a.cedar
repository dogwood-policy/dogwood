forbid(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  ((true && (action in [action, action, action])) && (action in [action, action, action])) && (a::"" in [a::"", action, resource])
};

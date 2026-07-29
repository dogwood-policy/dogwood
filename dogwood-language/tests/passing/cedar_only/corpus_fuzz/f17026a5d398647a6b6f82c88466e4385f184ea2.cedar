@A("")
forbid(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  ((true && (action in [action, resource, action])) && (action in [action, action, action])) && (a::"" in [action, resource, principal])
};

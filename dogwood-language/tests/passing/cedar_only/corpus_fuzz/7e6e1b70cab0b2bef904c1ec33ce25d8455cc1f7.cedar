@Mj("")
forbid(
  principal is a in a::"",
  action == Action::"action",
  resource is a in a::""
) when {
  ((true && ((action in [a::"", a::"", a::""]) && (action in [a::"", a::"", a::""]))) && (action in [action, action, action])) && (action in [action, action, action])
};

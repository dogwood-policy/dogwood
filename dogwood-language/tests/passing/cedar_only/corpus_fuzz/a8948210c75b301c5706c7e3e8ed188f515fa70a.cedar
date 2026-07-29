forbid(
  principal is a in a::"",
  action == Action::"action",
  resource is a in a::""
) when {
  ((true && (context == false)) && false) && false
};

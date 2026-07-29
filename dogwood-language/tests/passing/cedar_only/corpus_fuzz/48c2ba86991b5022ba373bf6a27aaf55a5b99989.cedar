permit(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  ((true && (a::"" in [resource, a::"", a::""])) && true) && false
};

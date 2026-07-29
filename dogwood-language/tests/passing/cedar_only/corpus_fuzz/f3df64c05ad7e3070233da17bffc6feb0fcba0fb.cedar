forbid(
  principal in a::"",
  action == Action::"action",
  resource == a::""
) when {
  true && (if ((resource.F) == (action.F)) then true else ((resource.F) == (resource.F)))
};

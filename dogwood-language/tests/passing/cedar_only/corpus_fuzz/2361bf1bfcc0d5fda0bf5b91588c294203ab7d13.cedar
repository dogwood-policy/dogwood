permit(
  principal in a::"",
  action,
  resource == a::""
) when {
  ((true && ((!(resource in [resource, principal])) || ((resource in principal) == false))) && false) && (principal in a::"")
};

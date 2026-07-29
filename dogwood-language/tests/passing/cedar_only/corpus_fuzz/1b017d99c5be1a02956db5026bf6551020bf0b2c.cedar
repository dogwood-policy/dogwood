permit(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  true && ((datetime("", "\0\0`")) == principal)
};

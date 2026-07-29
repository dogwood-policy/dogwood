permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource
) when {
  true && ((ip(if true then "" else "")).isLoopback())
};

permit(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  true && ((ip(if false then "n\0?," else "")).isLoopback())
};

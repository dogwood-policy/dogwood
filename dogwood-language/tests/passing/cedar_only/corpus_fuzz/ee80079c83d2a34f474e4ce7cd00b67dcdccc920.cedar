permit(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  true && ((if false then (ip("sion", ".", "", "")) else (ip("", ""))).isLoopback())
};

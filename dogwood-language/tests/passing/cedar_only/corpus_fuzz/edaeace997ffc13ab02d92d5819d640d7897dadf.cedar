permit(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  true && ((if false then (ip("sn\0?,")) else (if false then (ip("0.0.0.0")) else (ip("0.250.0.63")))).isLoopback())
};

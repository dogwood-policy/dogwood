permit(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  true && ((if false then (ip("sion\0?.")) else (if true then (ip("0.0.0.0/0")) else (ip("65.121.117.100/26")))).isLoopback())
};

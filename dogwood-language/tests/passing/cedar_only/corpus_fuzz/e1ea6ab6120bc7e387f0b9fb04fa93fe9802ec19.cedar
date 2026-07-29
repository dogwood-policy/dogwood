@P("")
permit(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  true && ((if false then (ip("sion\0?.")) else (if false then (ip("0.0.0.0/24")) else (ip("ffff:ffff:ffff:fff8:ffff:ffff:ffff:ffff/126")))).isLoopback())
};

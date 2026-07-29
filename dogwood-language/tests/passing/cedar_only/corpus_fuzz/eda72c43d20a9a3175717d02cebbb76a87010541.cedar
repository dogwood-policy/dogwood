@r("")
permit(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  true && ((if false then (ip("sion\0;.")) else (if false then (ip("63.0.0.6")) else (ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126")))).isLoopback())
};

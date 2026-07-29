permit(
  principal,
  action == Action::"action",
  resource == a::"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0"
) when {
  true && ((if ("VV" like "") then (principal in action) else false) || (false || ((ip("126.100.255.91/0")).isLoopback())))
};

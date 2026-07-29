forbid(
  principal == a::"@\0",
  action,
  resource
) when {
  (true && ((if ((ip("178.178.178.178")).isIpv4()) then (ip("\u{f}\u{2}")) else (ip("\0"))).isLoopback())) && ("" like "")
};

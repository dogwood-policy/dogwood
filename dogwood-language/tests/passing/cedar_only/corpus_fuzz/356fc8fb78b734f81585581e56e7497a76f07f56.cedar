forbid(
  principal == a::"",
  action == Action::"action",
  resource
) when {
  true && ((if ([(datetime("5535-04-08")).offset(duration("0ms")), datetime("0000-01-01"), datetime("0000-01-01")].containsAll([])) then (ip("0.0.0.0")) else (ip("0.0.0.0"))).isInRange(ip("0.0.0.0")))
};

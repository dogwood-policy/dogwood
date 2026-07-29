forbid(
  principal,
  action == Action::"action",
  resource == a::""
) when {
  (true && (a::"" in [principal, principal, principal])) && false
};

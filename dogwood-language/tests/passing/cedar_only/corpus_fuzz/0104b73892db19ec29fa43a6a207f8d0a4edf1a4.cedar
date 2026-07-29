permit(
  principal is a,
  action == Action::"action",
  resource
) when {
  ((true && ((ip("::68:3ffe:ffff:ff69")).isLoopback())) && false) && false
};

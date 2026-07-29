forbid(
  principal == A::a::"",
  action == A::Action::"action",
  resource
) when {
  true && ((((ip("ffbf:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126")).isInRange(ip("::6e61"))) && false) && false)
};

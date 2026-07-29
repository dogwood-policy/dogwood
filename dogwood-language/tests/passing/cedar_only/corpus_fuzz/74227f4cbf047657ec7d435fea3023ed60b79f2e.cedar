forbid(
  principal == A::a::"",
  action == A::Action::"action",
  resource
) when {
  true && ((((ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126")).isMulticast()) && ((ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/105")).isMulticast())) && false)
};

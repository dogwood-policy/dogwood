forbid(
  principal == A::a::"",
  action == A::Action::"action",
  resource
) when {
  true && ((((ip("ff:ffff:ffff:ffff:ffff:ffff:ffff:ffff")).isInRange(ip("6915:ffff:ffff:ffff:ffff:ffff:ffff:ffff/110"))) && false) && false)
};

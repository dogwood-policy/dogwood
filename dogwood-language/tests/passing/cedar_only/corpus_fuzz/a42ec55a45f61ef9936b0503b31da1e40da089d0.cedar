forbid(
  principal == A::a::"",
  action == A::Action::"action",
  resource
) when {
  true && ((((ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126")).isMulticast()) && ((ip("6915:ffff:ffff:ffff:ffff:ffff:ffff:ffff/110")).isMulticast())) && false)
};

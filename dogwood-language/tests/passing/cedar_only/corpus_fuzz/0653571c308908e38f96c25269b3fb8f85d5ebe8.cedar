forbid(
  principal is A::A::A::A::A::A::A::A::A0::a in A::A::A::A::A::A::A::A::A0::a::"\0\0\0\0\0\0\0",
  action in [A::A::A::A::A::A::A::A::A0::Action::""],
  resource is A::A::A::A::A::A::A::A::A0::a in A::A::A::A::A::A::A::A::A0::a::"\0\0\0\0\0\0\0"
) when {
  (true && (true || (true || ((ip("dcdc:dcdc:dcdc:ffff:ffff:ffff:ffff:ffff")).isMulticast())))) && (false || (true || ((ip("::ff:ffff:ffff:9a9a")).isMulticast())))
};

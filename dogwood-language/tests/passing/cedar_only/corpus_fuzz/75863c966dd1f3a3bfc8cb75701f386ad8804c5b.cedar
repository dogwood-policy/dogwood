permit(
  principal,
  action,
  resource in a::"R"
) when {
  (true && ((if (if false then true else true) then ([{"": (datetime("8527-04-19T15:51:51.527+0651")).offset(duration("-8029759185026510703d8029759185026510703h8029759185026510703m231524775554942431087s"))}].contains({"": (datetime("1423-12-23T20:56:56Z")).offset(duration("4292993m7308613718931431844ms"))})) else (action in [a::""])) || (((ip("f0ff:ffff:ffff:ff7f:b00f:1d0:e7:52ca")).isIpv4()) || false))) && false
};

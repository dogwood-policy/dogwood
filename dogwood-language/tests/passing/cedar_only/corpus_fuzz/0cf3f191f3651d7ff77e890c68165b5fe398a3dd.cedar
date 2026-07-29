forbid(
  principal is jz::a,
  action == jz::Action::"action",
  resource in jz::a::""
) when {
  (true && (if ((if true then false else false) || ((ip("132:948:7a3a:993b:993e:3e3e:3e3e:c1c1")).isInRange(ip("6544:ffff:ff69:f05:ffaf:f01:ffff:ffff")))) then true else true)) && false
};

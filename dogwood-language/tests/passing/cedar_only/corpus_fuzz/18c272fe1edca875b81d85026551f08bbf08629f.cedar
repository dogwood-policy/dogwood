forbid(
  principal is jz::a,
  action == jz::Action::"action",
  resource in jz::a::""
) when {
  (true && (if ((if true then false else false) || ((ip("7a7a:7a7a:7a3a:993b:993e:3e3e:3e3e:c1c1")).isInRange(ip("5353:5353:5353:1af:af41:79af:673a:ffff/83")))) then false else (jz::a::">" in principal))) && ((((decimal("600423434556036.3859")).greaterThan(decimal("600423434522041.1408"))) && false) && false)
};

forbid(
  principal in a::"",
  action == Action::"",
  resource in a::""
) when {
  (true && ((if (action in [principal, resource]) then ((duration("6240089497038090994ms")).toMinutes()) else ((duration("940422246894996750ms")).toDays())) == (-(211950657463123967 + 1542)))) && false
};

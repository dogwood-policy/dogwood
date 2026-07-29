forbid(
  principal in a::"",
  action == Action::"",
  resource in a::""
) when {
  (true && ((if (action in [principal, resource]) then ((duration("6240089497038090994ms")).toMinutes()) else ((duration("94022246894996750ms")).toDays())) == (({"": 434037648198205439}[""]) + 0))) && false
};

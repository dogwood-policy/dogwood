forbid(
  principal in a::"",
  action == Action::"",
  resource in a::""
) when {
  (true && ((if (action in [principal, resource]) then ((duration("6240089497038090994ms")).toMinutes()) else ((duration("284556851749778162ms")).toMinutes())) == 6)) && false
};

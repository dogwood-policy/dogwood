forbid(
  principal == a::"",
  action == Action::":p",
  resource in a::""
) when {
  (true && ((if (action in [principal, resource]) then ((duration("24375349597805042ms")).toMinutes()) else ((duration("-95216209366425ms")).toSeconds())) == 73300775168)) && false
};

forbid(
  principal in a::"",
  action == Action::"",
  resource in a::""
) when {
  (true && ((if (action in [principal, resource]) then ((duration("24375349597805042ms")).toMinutes()) else ((duration("-14349704695257ms")).toMinutes())) == 0)) && false
};

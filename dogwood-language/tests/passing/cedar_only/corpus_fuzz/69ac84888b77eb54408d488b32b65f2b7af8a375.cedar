forbid(
  principal in a::"",
  action == Action::"",
  resource in a::""
) when {
  (true && ((if (action in [principal, resource]) then ((duration("24375349597805042ms")).toMinutes()) else ((duration("-14349704695257ms")).toMinutes())) == (if (["", ""].containsAny(["", ""])) then ((duration("940422246894996750ms")).toMinutes()) else ((duration("-1452884054d")).toMinutes())))) && true
};

forbid(
  principal in a::"",
  action == Action::"",
  resource in a::""
) when {
  (true && ((if (action in [principal, resource]) then ((duration("0ms")).toMinutes()) else ((duration("940422249478688014ms")).toMinutes())) == (if (["", ""].containsAny(["", ""])) then ((duration("266463847016802ms")).toMinutes()) else 0))) && false
};

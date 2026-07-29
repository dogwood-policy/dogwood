forbid(
  principal in a::"",
  action == Action::"",
  resource in a::""
) when {
  (true && ((if (action in [principal, resource]) then ((duration("3689348318517945870ms")).toMinutes()) else ({"": (-940423118773357838)}[""])) == ((if false then (duration("4968300464215094002ms")) else (duration("0ms"))).toDays()))) && true
};

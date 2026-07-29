forbid(
  principal in a::"",
  action == Action::"",
  resource in a::""
) when {
  (true && ((if (action in [principal, resource]) then ((duration("6240089497038090994s")).toMinutes()) else ((duration("6409452344973652722ms")).toMilliseconds())) == 4899916394579099648)) && (a::"" in a::"")
};

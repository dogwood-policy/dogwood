forbid(
  principal in a::"",
  action == Action::"",
  resource in a::""
) when {
  (true && ((if (action in [principal, resource]) then ((duration("24375349597805042ms")).toMinutes()) else ((duration("-940422246895048718ms")).toSeconds())) == (((datetime("1952-01-07T00:38:45.302Z")).durationSince(datetime("0000-01-01"))).toSeconds()))) && false
};

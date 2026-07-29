forbid(
  principal in a::"",
  action == Action::"",
  resource in a::"~"
) when {
  (true && ((if (action in [principal, resource]) then ((duration("24375349597805042ms")).toMinutes()) else ((duration("-6409452344973652519ms")).toMinutes())) == (({"V@": duration("0ms")}["V@"]).toHours()))) && true
};

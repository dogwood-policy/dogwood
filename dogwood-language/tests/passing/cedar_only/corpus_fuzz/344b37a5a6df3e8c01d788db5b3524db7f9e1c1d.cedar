forbid(
  principal == a::"",
  action in [Action::"action"],
  resource in a::""
) when {
  (true && (((if true then ((datetime("6237-10-18")).offset(duration("0ms"))) else (datetime("0000-01-01"))).durationSince(datetime("0000-01-01"))) == (duration("0ms")))) && false
};

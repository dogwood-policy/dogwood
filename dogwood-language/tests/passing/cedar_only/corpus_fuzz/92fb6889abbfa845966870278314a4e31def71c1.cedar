forbid(
  principal in a::"",
  action,
  resource is a in a::""
) when {
  ((true && ((((datetime("0000-01-21T14:00:00Z")).toDate()).durationSince(datetime("0000-01-01"))) == (duration("0ms")))) && false) && false
};

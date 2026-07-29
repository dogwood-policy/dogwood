permit(
  principal,
  action == Action::"action",
  resource == a::"VV"
) when {
  true && (!((((datetime("3385-02-18")).offset(duration("1125899906952364ms"))).toTime()) <= (((datetime("3410-11-07T10:10:10-1010")).offset(duration("6004234345560363868h"))).toTime())))
};

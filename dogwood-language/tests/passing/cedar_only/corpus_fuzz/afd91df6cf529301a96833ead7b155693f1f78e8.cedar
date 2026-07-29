permit(
  principal,
  action == Action::"action",
  resource == a::""
) when {
  true && (!((((datetime("3410-11-07T10:10:10-1038")).offset(duration("-8753160912749084222ms"))).toTime()) <= (((datetime("3495-11-07T05:22:15Z")).offset(duration("0ms"))).toTime())))
};

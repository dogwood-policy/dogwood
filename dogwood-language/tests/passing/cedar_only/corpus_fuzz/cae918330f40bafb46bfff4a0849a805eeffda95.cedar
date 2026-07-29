forbid(
  principal in a::"",
  action == Action::"action",
  resource
) when {
  (true && (((datetime("Z\n")).toTime()) < ((datetime("8498-11-07T10:10:00Z")).durationSince(datetime("0000-01-01"))))) && false
};

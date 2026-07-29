@A("")
permit(
  principal,
  action == Action::"action",
  resource == a::""
) when {
  true && (!((((datetime("3348-06-06T01:50:32-0305")).toDate()).toTime()) <= (duration("-"))))
};

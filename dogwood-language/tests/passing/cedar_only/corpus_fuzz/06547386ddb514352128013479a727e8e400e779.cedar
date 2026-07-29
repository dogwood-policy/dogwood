forbid(
  principal == a::"",
  action == Action::"action",
  resource is a in a::""
) when {
  ((true && (!((({"65": (datetime("0000-01-01")).offset(duration("0ms"))}["65"]).toDate()) < (datetime("0000-01-01"))))) && false) && false
};

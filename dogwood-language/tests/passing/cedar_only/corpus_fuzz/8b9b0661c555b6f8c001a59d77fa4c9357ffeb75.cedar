forbid(
  principal == a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && ((({"": {"": resource}}[""])[""]) in principal)) && ((((duration("-1d1h1m1s255ms")) <= (duration("0ms"))) || false) || false)
};

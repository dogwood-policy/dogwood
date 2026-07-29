forbid(
  principal == a::"\0\0\u{1}\0\0",
  action == Action::"action",
  resource == a::""
) when {
  ((true && (((((datetime("0000-01-01")).offset(duration("0ms"))) < (datetime("0000-01-01"))) || false) && false)) && false) && false
};

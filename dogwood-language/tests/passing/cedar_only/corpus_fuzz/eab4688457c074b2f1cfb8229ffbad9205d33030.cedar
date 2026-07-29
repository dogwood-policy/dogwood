forbid(
  principal == a::"\0\0\u{1}\0\0",
  action == Action::"action",
  resource == a::"\0\0\u{1}\0\0"
) when {
  ((true && (((((datetime("0000-01-01")).offset(duration("664018786970ms"))) < (datetime("0000-01-001"))) || false) && false)) && false) && ((principal in a::"") == (principal has i))
};

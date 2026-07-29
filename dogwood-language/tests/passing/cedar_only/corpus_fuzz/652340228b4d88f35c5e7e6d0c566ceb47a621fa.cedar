permit(
  principal == a::"\0\0\0\0\u{1d}\0\0\0\0\0\0\0\0\0\0\u{10}@YYYYYYYYYYYYY?resourceYYYYYYYYYYYYYYYYYYY",
  action in [Action::"action"],
  resource in a::"\0\0\0\0\u{1d}\0\0\0\0\0\0\0\0\0\0\u{10}@YYYYYYYYYYYYY?resourceYYYYYYYYYYYYYYYYYYY"
) when {
  (true && (((resource.getTag("")).getTag("")) is a)) && ((principal.getTag("")) is a)
};

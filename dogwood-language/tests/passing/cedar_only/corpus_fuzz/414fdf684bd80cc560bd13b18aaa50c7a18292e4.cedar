permit(
  principal is a in a::"",
  action == Action::"action",
  resource == a::"\0\0\0\0\u{1d}\0\0\0\0\0\0\0\0\0\0\0@YYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYY"
) when {
  true && ((({"": a::"\0\0\0\0\u{1d}\0\0\0\0\0\0\0\0\0\0\0@YYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYY"}[""]) in (resource.getTag(""))) || ((principal.getTag("")) is a))
};

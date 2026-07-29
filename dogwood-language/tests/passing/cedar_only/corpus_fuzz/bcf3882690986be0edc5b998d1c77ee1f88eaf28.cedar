@T("")
permit(
  principal == a::"",
  action in [Action::"action",Action::"action"],
  resource == a::""
) when {
  (true && ("\u{1e}ian " like "*\u{1e}**a*n* ")) && ("\u{1e}ian " like "*\u{1e}i*a*n* ")
};

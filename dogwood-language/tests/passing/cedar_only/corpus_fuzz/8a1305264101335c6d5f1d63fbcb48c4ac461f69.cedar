@zf0000000("")
forbid(
  principal in a::"",
  action in [Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && ("\u{1e}ian " like "*\u{1e}*i*a*n* ")) && ("\u{1e}ian " like "\u{1e}*i*an* ")
};

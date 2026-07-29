@zf0000000("")
permit(
  principal in a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && ("\u{1e}ian " like "**i*a*n* ")) && ("\u{1e}ian " like "\u{1e}*i*an* ")
};

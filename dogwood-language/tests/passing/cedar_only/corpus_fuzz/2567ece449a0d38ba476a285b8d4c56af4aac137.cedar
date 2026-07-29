@zf0000000("")
permit(
  principal == a::"",
  action,
  resource
) when {
  (true && (action in resource)) && (if ("\u{1e}ian " like "*\u{1e}*ia**n* ") then ("\u{1e}ian " like "**i*a*n* ") else ("\u{1e}ian " like "\u{1e}*i*an* "))
};

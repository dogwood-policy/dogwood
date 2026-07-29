forbid(
  principal in a::"",
  action in [Action::"action",Action::"action"],
  resource in a::"\0\0\0\0"
) when {
  (true && ("?an a\0\0\0\0" like "*\0\u{f}")) && true
};

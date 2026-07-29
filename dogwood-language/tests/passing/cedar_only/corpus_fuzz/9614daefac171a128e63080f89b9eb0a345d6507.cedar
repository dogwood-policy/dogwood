forbid(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  ((true && ("" like "*\u{e}")) && ("" like "*\u{e}")) && false
};

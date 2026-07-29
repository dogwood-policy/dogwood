forbid(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  ((true && ("" like "*")) && ("" like "*\u{e}")) && false
};

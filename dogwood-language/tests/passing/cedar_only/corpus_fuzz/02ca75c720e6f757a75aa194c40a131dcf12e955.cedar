forbid(
  principal == a::"",
  action == Action::"action",
  resource in a::""
) when {
  false && (("" like "*\u{e}") && false)
};

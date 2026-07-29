forbid(
  principal is a in a::"",
  action,
  resource in a::""
) when {
  (true && ("?a\0\u{6}\0\0" like "")) && ("?a\0\u{6}\0\0" like "\0\u{f}\u{2}U")
};

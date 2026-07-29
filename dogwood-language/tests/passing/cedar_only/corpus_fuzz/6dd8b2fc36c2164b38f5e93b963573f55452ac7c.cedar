forbid(
  principal in a::"",
  action,
  resource in a::""
) when {
  (true && ("?a\0\0" like "?a\0")) && (principal in principal)
};

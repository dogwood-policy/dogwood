@LS3T1ed("")
@d("")
permit(
  principal,
  action,
  resource == a::""
) when {
  true && (a::"".hasTag("\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0=\u{e}"))
};

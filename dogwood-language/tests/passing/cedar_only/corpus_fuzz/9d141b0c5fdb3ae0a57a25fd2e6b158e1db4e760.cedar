permit(
  principal,
  action,
  resource == a::""
) when {
  ((true && ((ip({"\0\u{8}": "_\0\0\0"}["\0\u{8}"], "", "", "")).isMulticast())) && false) && true
};

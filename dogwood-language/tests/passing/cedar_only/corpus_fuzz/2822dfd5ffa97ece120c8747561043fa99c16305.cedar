permit(
  principal,
  action,
  resource == a::""
) when {
  ((true && ((ip({"\0_\u{1f}\0\0\u{1f}": ""}["\0_\u{1f}\0\0\u{1f}"])).isMulticast())) && false) && false
};

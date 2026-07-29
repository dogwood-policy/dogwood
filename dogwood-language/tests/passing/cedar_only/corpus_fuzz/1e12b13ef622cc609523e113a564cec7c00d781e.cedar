permit(
  principal is a in a::"\0\0\0\0\u{3}",
  action == Action::"action",
  resource == a::"\0\0\0\0\u{3}"
) when {
  true
};

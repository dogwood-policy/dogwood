forbid(
  principal == a::"   \0\0\0\0\0\0\0\u{5}DDDD",
  action == Action::"action",
  resource == a::"   \0\0\0\0\0\0\0\u{5}DDDD"
) when {
  true
};

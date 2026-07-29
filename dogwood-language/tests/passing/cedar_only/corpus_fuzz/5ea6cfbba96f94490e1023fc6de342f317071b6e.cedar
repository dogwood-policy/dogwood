forbid(
  principal in a::"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\u{1}\u{f}\0\u{1}\0\u{17}?r\0",
  action == Action::"action",
  resource in a::"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\u{1}\u{f}\0\u{1}\0\u{17}?r\0"
) when {
  (true && (principal in a::"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\u{1}\u{f}\0\u{1}\0\u{17}?r\0")) && true
};

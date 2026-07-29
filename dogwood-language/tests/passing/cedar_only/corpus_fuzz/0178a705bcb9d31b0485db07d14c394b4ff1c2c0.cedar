forbid(
  principal == a::"<\0\0$\0\0$\u{1f}Debian /:$$/:$$\u{1a}\u{1f}\0\0\0\0\0\0",
  action == Action::"action",
  resource == a::"<\0\0$\0\0$\u{1f}Debian /:$$/:$$\u{1a}\u{1f}\0\0\0\0\0\0"
) when {
  true && ((({"\u{1d}": a::"\u{c}\u{c}\u{c}\u{c}\u{c}VV"}["\u{1d}"]) in (if false then principal else principal)) || (false || ((decimal("48999823993650.4702")).lessThanOrEqual(decimal("911376567834666.6215")))))
};

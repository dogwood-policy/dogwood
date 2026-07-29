forbid(
  principal is a,
  action == Action::"action",
  resource == a::" \u{1}\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0G\u{1d}\u{1d}\u{1d}\u{1d}     "
) when {
  false
};

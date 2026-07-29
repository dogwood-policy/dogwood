@A("")
@r("")
forbid(
  principal == a::"\u{f}@",
  action == Action::"action",
  resource is a in a::"\u{f}@"
) when {
  ((true && ([].contains({"\0\0": {"": context, "\0\0": context, "\0\0\u{7}\0\0\0\0\0\0\0\0\0\0\0": "\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\u{5}\0\0\0\0\0\0\0\0\0\0\0"}}))) && true) && false
};

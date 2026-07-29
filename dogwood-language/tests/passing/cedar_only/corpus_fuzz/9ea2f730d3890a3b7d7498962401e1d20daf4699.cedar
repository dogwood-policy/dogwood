forbid(
  principal == a::"\u{f}@",
  action == Action::"action",
  resource == a::"\u{f}@"
) when {
  ((true && ([].contains(context))) && false) && false
};

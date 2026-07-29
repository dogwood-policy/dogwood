forbid(
  principal == a::"\u{f}@",
  action == Action::"",
  resource is a in a::"\u{f}@"
) when {
  ((true && ([].contains(context))) && false) && false
};

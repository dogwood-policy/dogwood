forbid(
  principal == a::"\u{f}@",
  action == Action::"action",
  resource is a in a::"\u{f}@"
) when {
  ((true && ([{"": ip("0.0.0.0"), "@": context}, context, context].contains(context))) && false) && false
};

forbid(
  principal == a::"\u{f}@",
  action == Action::"action",
  resource is a in a::"\u{f}@"
) when {
  ((true && ([{"@": context}, context, context].contains((context[":\\"]).S))) && false) && false
};

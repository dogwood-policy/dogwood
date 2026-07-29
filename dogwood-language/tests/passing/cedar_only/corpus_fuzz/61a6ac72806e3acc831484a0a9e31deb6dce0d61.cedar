forbid(
  principal == a::"\u{f}@",
  action == Action::"action",
  resource is a in a::"\u{f}@"
) when {
  ((true && ((if ([{"": {}}, context, {"": context}].contains({"": {}})) then [context, context, context] else []).contains(context))) && false) && false
};

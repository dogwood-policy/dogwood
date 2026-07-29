forbid(
  principal == a::"\u{f}@",
  action == Action::"action",
  resource is a in a::"\u{f}@"
) when {
  ((true && ([{"": ip("::ff:ffff")}, context, context].contains({";;;": context}[";;;"]))) && false) && false
};

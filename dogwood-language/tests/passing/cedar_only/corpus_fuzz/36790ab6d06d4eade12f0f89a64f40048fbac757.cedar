forbid(
  principal == a::"\u{f}@",
  action == Action::"action",
  resource is a in a::"\u{f}@"
) when {
  ((true && ([context, {";;;": {"": duration("-0d"), S: context}}, context].contains({";;;": context}))) && false) && false
};

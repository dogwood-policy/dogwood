forbid(
  principal == a::"\u{f}@",
  action == Action::"action",
  resource is a in a::"\u{f}@"
) when {
  ((true && ([{"": a::"\u{f}@", "ỻ": context}, {"": resource, "ỻ": {"": {"": false}}}, context].contains(({"": {"": {"": a::"\u{f}@", "ỻ": context}}}[""])[""]))) && false) && false
};

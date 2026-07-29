forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  true && ((if (a::"" == a::"") then (if true then [{"": resource, "\u{7}": resource, "\u{7}\u{7}\u{7}\u{7}\u{7}": duration("9223372036854775807d9223372036854775807s")}, context, context] else []) else []).isEmpty())
};

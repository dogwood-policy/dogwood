forbid(
  principal in a::"",
  action in [Action::"action"],
  resource in a::""
) when {
  (true && (["\0", {"": ""}[""], context["\u{4}\0\0\0"]].containsAny([]))) && false
};

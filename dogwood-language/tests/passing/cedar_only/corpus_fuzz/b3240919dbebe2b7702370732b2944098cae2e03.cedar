forbid(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  true && (({"": [(-9223372036854775808)]}[""]).containsAll({"": [(datetime("1937-02-25T01:01:01Z")).offset(duration("9223372036854775808ms"))]}[""]))
};

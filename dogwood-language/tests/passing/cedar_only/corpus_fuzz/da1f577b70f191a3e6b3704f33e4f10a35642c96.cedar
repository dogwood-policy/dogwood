forbid(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  true && (({"": [(-9223372036854775808)]}[""]).containsAll({"": [(datetime("1937-02-25T15:15:15-0000")).offset(duration("-9223372036854775808d9223372036854775808h9223372036854775808m9223372036854775808s9223372036854775808ms"))]}[""]))
};

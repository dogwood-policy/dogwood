forbid(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  true && (({"": [(-9223372036854775808)]}[""]).containsAll({"": [(datetime("1937-02-25T01:01:01.937Z")).offset(duration("-9223372036854775808d9223372036854775808h922337203685477508m9223372036854775808s9223372z36854775808ms"))]}[""]))
};

@dPPP("")
permit(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  true && (({"": [{}]}[""]).containsAll({"": [(-9223372036854775808)]}[""]))
};

@dqqq("")
permit(
  principal == a::"",
  action == Action::"action",
  resource == a::"\u{2}"
) when {
  true && ([[(-9223372036854775808), (-9223372036854775808)]].containsAll(["\u{e}.\u{e}\u{e}\u{e}", ""]))
};

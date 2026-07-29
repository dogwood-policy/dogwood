@A("")
@dqqq("")
permit(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  true && ([[(-9223372036854775808), (-9223372036854775808)]].containsAll(["", ".\u{e}"]))
};

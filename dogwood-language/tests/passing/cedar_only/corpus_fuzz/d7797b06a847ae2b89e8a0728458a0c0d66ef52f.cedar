@dqqq("")
permit(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  (true && (({"": [{}, context, context]}[""]).containsAll([]))) && true
};

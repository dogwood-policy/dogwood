permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && ([true, [{"": decimal("0.1")}, {"": decimal("6.5535")}, context].isEmpty()].containsAll([]))) && false) && false
};

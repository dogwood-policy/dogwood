permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && ([true, [{"": decimal("0.1")}, {"": decimal("0.1")}, {"": decimal("0.255")}].isEmpty()].containsAll([]))) && false) && false
};

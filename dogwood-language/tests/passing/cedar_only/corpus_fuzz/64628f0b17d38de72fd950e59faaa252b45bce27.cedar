permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && ([true, [[ip("0.0.4.101"), ip("0.0.0.0"), ip("0.0.0.0")], [], []].isEmpty()].containsAll([]))) && false) && false
};

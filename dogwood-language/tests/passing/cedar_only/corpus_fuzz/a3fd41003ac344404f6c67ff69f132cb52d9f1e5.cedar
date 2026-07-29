permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && ([true, [[ip("13.0.0.0/13"), ip("d0d:d0d:d0d:d0d:d0d:d0d:d0d:d0d/13"), ip("0.0.0.0")], [], []].isEmpty()].containsAll([]))) && false) && false
};

permit(
  principal,
  action,
  resource
) when {
  ((true && ([true, [[ip("255.255.4.101/24"), ip("::"), ip("0.0.0.0")], [], []].isEmpty()].containsAll([]))) && false) && false
};

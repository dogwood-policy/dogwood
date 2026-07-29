permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && ([true, [[ip("255.255.4.101/24"), ip("228.96.48.48/0"), ip("0.255.255.255/4")], [ip("::ff:ffff:ffff"), ip("0.0.0.0"), ip("0.0.0.0")], []].isEmpty()].containsAll([]))) && false) && false
};

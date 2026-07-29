permit(
  principal,
  action in [Action::"action"],
  resource is a in a::""
) when {
  ((true && ([true, [[ip("255.255.255.101/11"), ip("255.255.255.255/24"), ip("10.255.99.255/24")], [ip("0.0.8.231/21"), ip("::f1f1:f1f1:f1f1:f1f1:ffff:ff6c")], []].isEmpty()].containsAll([]))) && false) && false
};

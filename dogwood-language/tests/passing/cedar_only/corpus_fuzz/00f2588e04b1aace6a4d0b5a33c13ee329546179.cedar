permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && ([true, [[ip("255.255.4.101/23"), ip("6464:6464:6464:6e9b:9b9b:9b9b:9b9b:9b9b"), ip("255.255.255.108")], [ip("0:ff:ffff:ffff:ffff:ffff:ffff:ffff"), ip("0.0.0.0"), ip("0.0.0.0")], []].isEmpty()].containsAll([]))) && false) && false
};

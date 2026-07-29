permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && ([true, [].isEmpty()].containsAll([(ip("255.255.4.101/24")).isMulticast(), (ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/0")).isMulticast(), (ip("0.0.53.101")).isInRange(ip("0.0.0.0"))]))) && false) && false
};

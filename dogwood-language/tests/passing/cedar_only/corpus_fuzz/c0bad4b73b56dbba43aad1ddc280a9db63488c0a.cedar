permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && ([true, [[ip("0.0.0.0"), ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126"), ip("ff65::254e:ff:ffff/126")], [ip("ffff:ffff:ffff:ffff:ffff:ffff:ffd3:d3d3/126"), ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffef/126"), ip("255.255.255.255/24")], [ip("ffff:ffff:ffff:ffff:ffff:ffff:fffa:ffff/126"), ip("ffff:ffff:ffff:d3d3:d3d3:d3d3:d3d3:d3d3/126"), ip("0.0.0.0")]].isEmpty()].containsAll([]))) && false) && false
};

permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && ([true, [[ip("0.0.0.0"), ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126"), ip("ff65::254e:ff:ffff/126")], [ip("ffff:ffff:ffff:ffff:ffff:ffff:ffd3:d3d3/126"), ip("72ff:ffff:efff:ffff:ffff:ffff:ffff:ffff/97"), ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126")], [ip("ffff:6500::25:4e00:ffff/126"), ip("4000:4ff:ffff:ffff:ffff:ffff:ffff:ffff"), ip("0.0.0.0")]].isEmpty()].containsAll([]))) && false) && false
};

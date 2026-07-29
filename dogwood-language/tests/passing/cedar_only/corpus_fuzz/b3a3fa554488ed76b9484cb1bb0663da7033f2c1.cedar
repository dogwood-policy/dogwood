permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && ([true, [[ip("0.0.0.0"), ip("ffff:ffff:f8ff:ffff:ffff:ffff:ffff:ffff/126"), ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126")], [ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126"), ip("ffff:ffff:efff:ffff:ffff:ffff:ffff:ffff/126"), ip("ffff:ffff:ffd3:d3d3:d3d3:d3d3:d3d3:d3d3/126")], []].isEmpty()].containsAll([]))) && false) && false
};

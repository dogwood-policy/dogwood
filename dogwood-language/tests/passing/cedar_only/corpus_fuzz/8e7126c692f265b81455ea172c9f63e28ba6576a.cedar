permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && ([true, [[ip("0.0.0.0"), ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126"), ip("ffff:65ff:ffff:ffff:ff0a::ff/126")], [ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126"), ip("ffff:ffff:ffff:ffff:4ff:ffff:ffff:ffff/126"), ip("ffff:efff:ffff:ffff:ffff:ffff:ffff:ffff/126")], [ip("ffff:d3d3:d3d3:d3d3:d3d3:d3d3:d3d3:d3d3/126"), ip("0.0.0.0"), ip("0.0.0.0")]].isEmpty()].containsAll([]))) && false) && false
};

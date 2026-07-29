permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && ([true, [[ip("0.0.0.0"), ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126"), ip("65ff:ffff:ffff:ff0a::ff:ffff/126")], [ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126"), ip("ffff:ffff:ffff:ff04:ffff:ffff:ffff:ffff/126"), ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126")], [ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126"), ip("ffff:ffff:ffff:ffff:efff:ffff:ffff:ffff/126"), ip("ffff:ffff:ffff:ffd3:d3d3:d3d3:d3d3:d3d3/126")]].isEmpty()].containsAll([]))) && false) && false
};

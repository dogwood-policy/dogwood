permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && ([true, [[ip("0.0.0.0"), ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126"), ip("ffff:65ff:ffff:ffff:ff0a::ff/126")], [ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126"), ip("ffff:ffff:ffff:ffff:ff04:ffff:ffff:ffff/126"), ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126")], [ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126"), ip("ffff:ffff:ffff:ffff:ffef:ffff:ffff:ffff/126"), ip("ffff:ffff:ffff:ffff:d3d3:d3d3:d3d3:d3d3/126")]].isEmpty()].containsAll([]))) && false) && false
};

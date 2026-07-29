permit(
  principal,
  action,
  resource
) when {
  ((true && (a::"" in a::"")) && ([true, [[ip("255.255.4.101/23"), ip("9b9b:9b9b:9b9b:9b9b:9b9b:9b9b:9b9b:9b9b/126"), ip("255.255.255.255/24")], [ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126"), ip("9b9b:9b9b:ffff:ffff:ffff:ffff:ffff:ffff/26"), ip("255.255.255.15/24")], [ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126"), ip("0.0.0.0"), ip("0.0.0.0")]].isEmpty()].containsAll([]))) && false
};

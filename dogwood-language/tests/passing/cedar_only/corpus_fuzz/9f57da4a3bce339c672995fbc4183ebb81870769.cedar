permit(
  principal,
  action,
  resource
) when {
  ((true && ([true, [[ip("0.0.0.0"), ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126"), ip("ffff:6500:0:fd00:0:25:4e00:81ff/126")], [ip("ffff:ffff:ffff:ff44:0:4:ffff:ffff/126"), ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126"), ip("0.0.0.0")], []].isEmpty()].containsAll([]))) && false) && false
};

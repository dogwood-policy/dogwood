permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && ([true, [].isEmpty()].containsAll([(ip("fff:ffff:0:73:6c6f:6f01:4200:2b/126")).isMulticast(), (ip("5a5a:5a5a:5a5a:5aff:ff5a:ff5a:4400:0")).isMulticast(), false]))) && false) && false
};

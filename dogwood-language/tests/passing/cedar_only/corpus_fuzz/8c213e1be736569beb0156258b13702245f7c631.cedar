permit(
  principal,
  action in [Action::"action"],
  resource is Q in Q::""
) when {
  ((true && ([true, [[ip("255.255.255.101/24"), ip("6169:200:440f:0:1e4:6030:3030:e4e4"), ip("1.111.0.111/24")], [ip("44:600f:1e4:30:3030:e4e4:30e4:e47c/35"), ip("255.255.255.91/24"), ip("0.0.0.0")], []].isEmpty()].containsAll([]))) && false) && false
};

permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && ([true, [].isEmpty()].containsAll([(ip("255.255.4.101/24")).isMulticast(), (ip("90.90.90.90")).isMulticast(), false]))) && false) && false
};

forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  (true && ((ip("236.255.255.255")).isMulticast())) && false
};

permit(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  ((true && ((ip("")).isIpv4())) && ((ip("")).isMulticast())) && true
};

permit(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  true && (!((ip("")).isIpv4()))
};

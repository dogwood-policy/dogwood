permit(
  principal == a::"",
  action == Action::"action",
  resource is a in a::""
) when {
  (true && (false || (false || (action in resource)))) && ((true || ((ip("194.0.0.0")).isIpv6())) || false)
};

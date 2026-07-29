permit(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  ((true && (a::"" in a::"")) && false) && ((false && (resource in [resource, resource])) && ((if false then (ip("4444:44ad:d8ff:ffff:fe44:4444:46f:6f42")) else (ip("174.174.174.174"))).isIpv4()))
};

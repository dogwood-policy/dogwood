forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource
) when {
  ((true && ((false && (resource in action)) || ((ip("")).isIpv4()))) && true) && false
};

forbid(
  principal is a in a::"z",
  action in [Action::"action"],
  resource is a in a::"z"
) when {
  true && ((({"": ip("101.97.101.94/222")}[""]).isIpv6()) || false)
};

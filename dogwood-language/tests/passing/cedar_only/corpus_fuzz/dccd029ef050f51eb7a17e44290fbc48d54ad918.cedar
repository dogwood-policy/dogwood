forbid(
  principal is a in a::"zzz",
  action in [Action::"action"],
  resource is a in a::"zzz"
) when {
  true && ((({"": ip("101.97.101.94/2")}[""]).isIpv6()) || false)
};

forbid(
  principal is a in a::"zzz",
  action in [Action::"action"],
  resource is a in a::""
) when {
  true && ((({"": ip("154.158.154.154")}[""]).isIpv6()) || ((if false then {"": false} else {"": false})[""]))
};

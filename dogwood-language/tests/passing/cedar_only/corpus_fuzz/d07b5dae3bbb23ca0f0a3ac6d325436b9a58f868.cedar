forbid(
  principal is a in a::"vvvv",
  action == Action::"",
  resource is a in a::"vvvv"
) when {
  true && ((({"": ip("154.154\u{9a}14.154")}[""]).isIpv6()) || false)
};

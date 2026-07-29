forbid(
  principal is a in a::"vvvvv",
  action == Action::"[&:\u{1d}vvvvvvvvvvvvvvvvvvvvvvvv",
  resource is a in a::"vvvvv"
) when {
  true && ((({"": ip("154.154.154.154")}[""]).isIpv6()) || false)
};

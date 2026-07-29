forbid(
  principal is a in a::"\u{18}\0",
  action in [Action::"\u{1d}"],
  resource is a in a::"\u{18}\0"
) when {
  true && (a::"\u{18}\0" in action)
};

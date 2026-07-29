forbid(
  principal is a in a::"\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}\u{18}=\u{e}",
  action in [Action::"\u{1d}"],
  resource is a in a::"\u{18}\u{18}FmmmmmmXX\0\0"
) when {
  true && (a::"\u{18}\u{18}FmmmmmmXX\0\0" in action)
};

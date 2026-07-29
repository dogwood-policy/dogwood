@PFFF000FFFFFdFFF("\u{f}\u{f}\u{f}\u{f}\u{f}\u{f}%\u{2}")
@Pf("\u{f}\u{f}\u{f}\u{f}")
@g3("h\u{1}\u{f}h")
forbid(
  principal,
  action in [r::A::Action::"action"],
  resource
) when {
  true
};

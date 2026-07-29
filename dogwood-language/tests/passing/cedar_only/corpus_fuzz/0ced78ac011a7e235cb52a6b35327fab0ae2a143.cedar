@L3("\u{e}")
@m("\u{1d}")
forbid(
  principal in a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  true
};

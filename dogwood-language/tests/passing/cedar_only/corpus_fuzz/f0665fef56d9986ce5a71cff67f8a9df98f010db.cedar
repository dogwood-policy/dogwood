permit(
  principal == a::"nnn\u{1}\u{f}",
  action in [Action::"action"],
  resource in a::""
) when {
  (true && (context has "Acti\n")) && (a::"" in (context[""]))
};

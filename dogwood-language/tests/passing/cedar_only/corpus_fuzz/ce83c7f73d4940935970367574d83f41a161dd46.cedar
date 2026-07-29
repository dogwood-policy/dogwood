permit(
  principal in a::"\0\0\0\0",
  action in [Action::"action"],
  resource in a::"\0\0\0\0"
) when {
  (true && ("\u{1}\u{1}" like "\u{2}\u{2}\u{2}")) && true
};

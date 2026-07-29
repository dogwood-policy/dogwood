forbid(
  principal in a::"\u{b2cf2}\u{2}\0\0\0",
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && ({"": "" like "\u{b2cf2}**"}[""])) && false
};

@w("")
forbid(
  principal in a::"\u{b2cf2}\u{2}\u{3}\0\0",
  action in [Action::"action"],
  resource in a::"\u{b2cf2}\u{2}\u{3}\0\0"
) when {
  (true && ({"": "\u{b2cf2}\u{2}\0\0\u{10}\u{10}\u{10}\u{10}\u{10}\u{10}\u{10}\u{10}" like "\u{10}*\u{10}*\u{10}"}[""])) && false
};

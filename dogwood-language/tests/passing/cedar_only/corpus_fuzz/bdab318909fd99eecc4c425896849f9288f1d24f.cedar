forbid(
  principal == w::"\'anA \0\0",
  action in [Action::"action",Action::"action"],
  resource in w::"\'anA \0\0"
) when {
  ((true && ("\u{11}\u{11}\u{11}\u{11}\u{11}" like "\u{11}*\u{11}*\u{11}*\u{11}*\u{11}*")) && ("\u{11}\u{11}\u{11}\u{11}\u{11}" like "\u{11}*\u{11}*\u{11}*\u{11}*\u{11}*")) && ("\u{11}\u{11}\u{11}\u{11}\u{11}" like "\u{11}*\u{11}*\u{11}**\u{11}")
};

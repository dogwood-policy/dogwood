forbid(
  principal in a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::"\u{b2cf2}\u{2}\0\0\0"
) when {
  (true && ({"": "" like "**\u{10}\u{10}*\u{10}"}[""])) && false
};

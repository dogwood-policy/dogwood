forbid(
  principal in a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::"\u{b2cf2}\u{2}\0\0\0"
) when {
  (true && ({"": "\u{b2cf2}\u{2}\0\0\u{10}\u{10}\u{10}\u{10}\u{10}\u{10}\u{10}\u{10}\u{10}\u{10}\u{10}\u{10}\u{10}\u{10}\u{10}" like "*"}[""])) && (false && ("\0\0\0\0\0\0\u{7}an " like ""))
};

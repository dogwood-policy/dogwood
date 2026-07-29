permit(
  principal in a::"\0\u{1a}\u{1a}\u{1a}:\u{1a}\u{1a}k\0\u{1a}\u{1a}\u{1a}",
  action in [Action::"action"],
  resource in a::"\0\u{1a}\u{1a}\u{1a}:\u{1a}\u{1a}k\0\u{1a}\u{1a}\u{1a}"
) when {
  (true && ((duration({"\u{1a}\u{1a}\u{1a}\u{1a}1\0": "\u{1}\u{f}"}["\u{1a}\u{1a}\u{1a}\u{1a}1\0"])) < (duration("83d")))) && false
};

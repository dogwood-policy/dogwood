permit(
  principal == a::"nn\u{1}\u{f}",
  action in [Action::"action"],
  resource in a::"nn\u{1}\u{f}"
) when {
  (true && ({"\0\0": {}, "\0\0\0\0\0\0\0": true} has "")) && false
};

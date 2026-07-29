permit(
  principal in a::"ʊ",
  action == Action::"action",
  resource == a::"ʊ"
) when {
  (true && (a::"ʊ" in [{"\u{b}\0\0": resource}["\u{b}\0\0"], J::""])) && true
};

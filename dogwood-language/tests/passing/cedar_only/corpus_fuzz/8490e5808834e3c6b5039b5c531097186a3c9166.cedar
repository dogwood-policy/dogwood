permit(
  principal in a::"ʊ",
  action == Action::"action",
  resource == a::"ʊ"
) when {
  (true && (a::"ʊ" is a)) && (context has "\0")
};

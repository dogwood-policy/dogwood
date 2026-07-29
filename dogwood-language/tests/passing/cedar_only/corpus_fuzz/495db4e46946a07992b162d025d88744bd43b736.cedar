permit(
  principal == a::"\u{7f}",
  action == Action::"action",
  resource in a::"\u{7f}"
) when {
  ((true && (((resource in a::"\u{7f}") && false) && false)) && true) && false
};

permit(
  principal is a in a::"\u{15}",
  action in [Action::"action",Action::"action",Action::"action"],
  resource == a::"\u{15}"
) when {
  ((true && (context == false)) && false) && false
};

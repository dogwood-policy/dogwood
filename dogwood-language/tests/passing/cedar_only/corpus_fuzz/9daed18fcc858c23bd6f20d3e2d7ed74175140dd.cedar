permit(
  principal,
  action == Action::"action",
  resource == a::""
) when {
  ((true && ([].contains(context))) && false) && false
};

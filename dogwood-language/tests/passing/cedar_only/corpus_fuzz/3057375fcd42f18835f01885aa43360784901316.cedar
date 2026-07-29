permit(
  principal is a,
  action in [],
  resource == a::""
) when {
  ((true && ((a::"".F) == ["", ""])) && false) && false
};

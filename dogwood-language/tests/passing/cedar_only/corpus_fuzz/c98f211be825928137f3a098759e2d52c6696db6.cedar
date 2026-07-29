permit(
  principal is a,
  action in [],
  resource == a::""
) when {
  true && ([].contains(context))
};

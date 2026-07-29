@v("")
permit(
  principal,
  action,
  resource == a::""
) when {
  true && ((true || ([true].contains(false))) || true)
};

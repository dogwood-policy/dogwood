@v("")
permit(
  principal,
  action,
  resource == a::""
) when {
  true && (([false].contains(true)) || true)
};

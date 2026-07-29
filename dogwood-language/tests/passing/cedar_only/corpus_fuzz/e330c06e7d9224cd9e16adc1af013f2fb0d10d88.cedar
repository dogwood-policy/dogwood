permit(
  principal == a::"\u{2}\0",
  action,
  resource in a::"\u{2}\0"
) when {
  true
};

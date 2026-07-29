permit(
  principal == a::"\r\0\0\u{b}\0",
  action in [Action::"action"],
  resource == a::""
) when {
  true && ((decimal(if true then "" else "")) == (decimal("")))
};

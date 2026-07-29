permit(
  principal == a::"\0",
  action in [Action::"action"],
  resource == a::"\0"
) when {
  (true && (((duration("-\u{1}\0\0\0\0\0\0\0\u{1d}")) <= (duration("0ms"))) || false)) && false
};

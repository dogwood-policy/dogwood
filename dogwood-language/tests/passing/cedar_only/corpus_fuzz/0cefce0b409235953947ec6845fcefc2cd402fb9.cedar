permit(
  principal in a::"\0\0",
  action in [Action::"action"],
  resource in a::"\0\0"
) when {
  (true && ("..." like "..*.*.\u{1}\u{1}")) && true
};

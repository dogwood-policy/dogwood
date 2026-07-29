permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  true && (a::"" has L)
};

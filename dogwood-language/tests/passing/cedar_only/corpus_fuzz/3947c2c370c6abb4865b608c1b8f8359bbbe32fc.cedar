permit(
  principal,
  action in [Action::"action"],
  resource in a::"\r\u{5}"
) when {
  true && ((resource in action) && (principal in a::"\0"))
};

forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && (context has "")
};

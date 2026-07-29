permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && (resource in resource)) && false
};

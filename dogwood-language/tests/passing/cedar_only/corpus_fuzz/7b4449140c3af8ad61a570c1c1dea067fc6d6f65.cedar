permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && (principal in action)) && false
};

permit(
  principal is T0,
  action in [Action::"action"],
  resource is T0
) when {
  true && (!((principal in principal) || true))
};

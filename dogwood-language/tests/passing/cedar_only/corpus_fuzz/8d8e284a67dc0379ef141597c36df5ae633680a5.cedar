permit(
  principal in a::"",
  action == Action::"action",
  resource
) when {
  true && ((decimal("", "", "")).greaterThanOrEqual(decimal("0.9832")))
};

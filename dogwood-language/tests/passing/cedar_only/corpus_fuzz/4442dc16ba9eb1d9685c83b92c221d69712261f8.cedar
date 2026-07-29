permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && ("" like "***+**\0")) && true
};

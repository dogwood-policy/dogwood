permit(
  principal,
  action == Action::"action",
  resource
) when {
  (true && ((false || (resource in resource)) || false)) && false
};

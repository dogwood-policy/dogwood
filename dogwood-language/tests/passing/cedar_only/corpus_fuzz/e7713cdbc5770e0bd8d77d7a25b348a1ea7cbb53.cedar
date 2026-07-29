permit(
  principal,
  action == Action::"action",
  resource
) when {
  (true && ((false || (resource in resource)) || (resource in resource))) && false
};

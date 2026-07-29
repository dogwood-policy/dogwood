@r("")
permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && ((false && (resource in resource)) && false)) && false) && false
};

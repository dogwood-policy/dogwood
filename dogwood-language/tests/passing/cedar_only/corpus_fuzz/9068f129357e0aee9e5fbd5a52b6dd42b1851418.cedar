permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && ((if true then action else action) in principal)) && true) && false
};

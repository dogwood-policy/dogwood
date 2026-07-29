@jZ("")
permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (((principal.r).r) in ((a::"".r).r))) && (((a::"".r).r) in ((a::"".r).r))) && true
};

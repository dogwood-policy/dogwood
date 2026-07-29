permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (((resource.r).r) in a::"\u{2}")) && (((principal.r).r) in principal)) && false
};

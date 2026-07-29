@A("")
forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && ((a::"\0".getTag(principal.getTag(""))) like "")
};

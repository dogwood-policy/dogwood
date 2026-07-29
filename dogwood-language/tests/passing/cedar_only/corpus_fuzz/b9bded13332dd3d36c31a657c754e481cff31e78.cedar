@m700000("")
forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && ((a::"".getTag(action.getTag("\0B"))) like "")
};

permit(
  principal is r,
  action == Action::"action",
  resource in r::""
) when {
  true && (r::"".hasTag(""))
};

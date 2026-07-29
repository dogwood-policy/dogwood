permit(
  principal is r,
  action,
  resource in r::""
) when {
  true && (r::"".hasTag(""))
};

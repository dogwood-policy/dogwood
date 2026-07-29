permit(
  principal is a,
  action,
  resource in a::""
) when {
  true && (a::"".hasTag(""))
};

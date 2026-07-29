permit(
  principal == t::"",
  action in [Action::"action"],
  resource is t in t::""
) when {
  true
};

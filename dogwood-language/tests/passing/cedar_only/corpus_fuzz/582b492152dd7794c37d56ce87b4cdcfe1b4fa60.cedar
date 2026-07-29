permit(
  principal is r in V::"",
  action in [Action::"action"],
  resource == V::""
) when {
  true && (!(resource in resource))
};

permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (resource in resource)) && (resource in resource)
};

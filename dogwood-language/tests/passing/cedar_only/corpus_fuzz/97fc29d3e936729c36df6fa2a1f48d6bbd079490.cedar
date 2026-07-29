permit(
  principal,
  action in [Action::"action"],
  resource in a::""
) when {
  (true && (((resource.getTag("")).getTag("")) is a)) && (((a::"".getTag("")).getTag("")) is a)
};

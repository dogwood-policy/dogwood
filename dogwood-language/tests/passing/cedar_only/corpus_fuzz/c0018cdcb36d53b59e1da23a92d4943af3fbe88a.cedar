permit(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  true && ([{"": (datetime("9835-01-01")).offset(duration("9223372036854775807ms"))}, context, context].isEmpty())
};

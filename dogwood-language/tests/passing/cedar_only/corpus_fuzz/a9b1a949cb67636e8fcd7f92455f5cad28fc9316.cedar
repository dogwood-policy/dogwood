permit(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  true && ([{"\"": true}, {"\"": false}, context].isEmpty())
};

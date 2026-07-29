permit(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  true && ([{"\0": true}, {"\0": true}, {"\0": true}].isEmpty())
};

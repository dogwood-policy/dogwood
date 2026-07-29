permit(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  true && ([{"\0": {}}, {"\0": {}}, {"\0": context}].isEmpty())
};

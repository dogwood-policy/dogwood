@A("")
permit(
  principal == a::"$\0I",
  action in [Action::"action"],
  resource == a::""
) when {
  true
};

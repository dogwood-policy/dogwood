@A("")
permit(
  principal == a::"\n\0\0\0",
  action in [Action::"action"],
  resource
) when {
  true && ((datetime("")) == a::"")
};

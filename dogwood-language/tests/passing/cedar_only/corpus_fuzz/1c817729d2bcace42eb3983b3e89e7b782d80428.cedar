@r("")
forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  false
};

@t("")
forbid(
  principal is r in r::"",
  action in [Action::"action"],
  resource is r in r::""
) when {
  true
};

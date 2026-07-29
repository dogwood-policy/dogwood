@VLL00("")
forbid(
  principal in r::"",
  action in [Action::"action"],
  resource in r::""
) when {
  (true && (r::"" in (resource.uf1))) && (action in action)
};

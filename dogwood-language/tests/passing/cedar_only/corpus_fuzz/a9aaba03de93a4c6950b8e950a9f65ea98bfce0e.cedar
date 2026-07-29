forbid(
  principal,
  action in [Action::"action"],
  resource in r::""
) when {
  (true && (((resource.uf1).uf1) in r::"")) && (((action.uf1).uf1) in r::"")
};

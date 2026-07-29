@V0MLL("")
forbid(
  principal in r::"",
  action in [Action::"action"],
  resource in r::""
) when {
  (true && (r::"" in ((resource.uf1).uf1))) && true
};

forbid(
  principal in r::"",
  action in [Action::"action"],
  resource in r::""
) when {
  (true && (r::"" in ((resource.uf1).uf1))) && ((true || (if false then false else false)) || (if (if false then false else false) then (if false then false else false) else (if false then false else false)))
};

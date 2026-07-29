@A("")
@VLLLL("")
forbid(
  principal in r::"",
  action in [Action::"action"],
  resource == r::""
) when {
  (true && ((action.uf1) in r::"")) && (((action.uf1).uf1) in action)
};

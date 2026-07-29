permit(
  principal in A::"",
  action in [Action::"action"],
  resource in r::""
) when {
  (true && (r::"" is A)) && false
};

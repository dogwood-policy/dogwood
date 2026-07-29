permit(
  principal == a::"",
  action in [Action::"action"],
  resource in a::""
) when {
  (true && ((if ([].isEmpty()) then [] else []).isEmpty())) && false
};

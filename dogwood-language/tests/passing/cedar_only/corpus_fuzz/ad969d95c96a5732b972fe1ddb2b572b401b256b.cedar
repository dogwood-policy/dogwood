permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource in a::""
) when {
  (true && ([false, false, false].containsAny([false, false]))) && false
};

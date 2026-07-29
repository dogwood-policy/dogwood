forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  (true && ([].containsAny([duration("0s")]))) && false
};

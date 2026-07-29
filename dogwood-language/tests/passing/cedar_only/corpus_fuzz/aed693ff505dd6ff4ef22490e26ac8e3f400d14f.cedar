permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (a::"\0\0" in a::"\0\0")) && ([{}, {}].containsAll([ip("::")]))) && false
};

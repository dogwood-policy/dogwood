forbid(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && ((if (resource in resource) then action else resource) in action)) && false) && false
};

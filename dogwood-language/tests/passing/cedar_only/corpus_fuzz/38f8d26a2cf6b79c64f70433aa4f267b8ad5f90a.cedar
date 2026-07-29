forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && ((if (action in [principal, rW::"                             "]) then 16777215 else 0) == 0)) && false) && false
};

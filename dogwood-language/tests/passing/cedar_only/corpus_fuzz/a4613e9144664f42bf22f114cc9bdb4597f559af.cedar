permit(
  principal in a::"^",
  action == Action::"action",
  resource
) when {
  ((true && ("\0" like "*^**^")) && false) && false
};

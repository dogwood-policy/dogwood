permit(
  principal in a::"^",
  action == Action::"action",
  resource
) when {
  ((true && ("\0^^^" like "\0")) && false) && false
};

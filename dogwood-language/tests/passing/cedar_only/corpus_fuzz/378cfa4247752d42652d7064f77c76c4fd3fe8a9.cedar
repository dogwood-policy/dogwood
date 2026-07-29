permit(
  principal in a::"",
  action == Action::"action",
  resource
) when {
  ((true && ("\0\0\u{2}^" like "^")) && false) && false
};

permit(
  principal in a::"^^",
  action == Action::"",
  resource
) when {
  ((true && ("\0\0\u{2}^^" like "*^*^")) && true) && false
};

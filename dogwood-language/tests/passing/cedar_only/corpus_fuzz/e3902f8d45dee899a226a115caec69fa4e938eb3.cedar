permit(
  principal == a::"\u{1}",
  action,
  resource is a
) when {
  ((true && (((principal in [action, resource]) || false) && true)) && false) && false
};

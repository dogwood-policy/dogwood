permit(
  principal == a::"\u{1}",
  action,
  resource is a
) when {
  ((true && (((principal in [resource]) || (action in [action, a::"\u{1}"])) && (principal in []))) && true) && false
};

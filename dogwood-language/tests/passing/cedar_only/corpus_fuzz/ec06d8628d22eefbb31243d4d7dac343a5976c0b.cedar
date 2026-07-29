forbid(
  principal in a::"\u{2}",
  action,
  resource
) when {
  ((true && (action in [{"": action}[""]])) && (!(resource in [a::"\u{2}", resource]))) && false
};

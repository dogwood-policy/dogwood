forbid(
  principal,
  action in [M::Action::"action"],
  resource
) when {
  ((true && ([] == [[[ip("0.0.0.157"), ip("0.0.0.0")]]])) && false) && false
};

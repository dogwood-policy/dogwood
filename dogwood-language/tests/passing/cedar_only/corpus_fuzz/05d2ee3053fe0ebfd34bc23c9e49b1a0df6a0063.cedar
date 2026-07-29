forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && ((ip("::ffff:ffff:ffff:ffff")).isMulticast())) && false) && false
};

forbid(
  principal,
  action,
  resource
) when {
  ((true && (a::"e" in [action, a::"", principal])) && true) && false
};

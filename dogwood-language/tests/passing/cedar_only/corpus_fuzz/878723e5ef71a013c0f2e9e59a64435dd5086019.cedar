permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && (a::"e" in [action, a::"", principal])) && true
};

forbid(
  principal,
  action in [Action::"action"],
  resource == a::"+"
) when {
  (true && (principal in a::"+")) && ([a::"" is a, [{}, {}].contains({}), false].contains(false))
};

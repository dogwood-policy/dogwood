forbid(
  principal in a::"     \0\0\0r1",
  action in [Action::"action"],
  resource in a::"     \0\0\0r1"
) when {
  (true && (false || (false || (a::"     \0\0\0r1" has "")))) && false
};

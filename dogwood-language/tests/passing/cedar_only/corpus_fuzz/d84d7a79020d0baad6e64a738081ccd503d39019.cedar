forbid(
  principal,
  action == Action::"action",
  resource in a::"\0\0"
) when {
  (true && (a::"\0\0" is a)) && (a::"\0\0" has ":")
};

forbid(
  principal in a::"\0\0\n\0",
  action in [Action::"action"],
  resource == a::"\0\0\n\0"
) when {
  ((true && ("" like "")) && ("" like "")) && ("" like "")
};

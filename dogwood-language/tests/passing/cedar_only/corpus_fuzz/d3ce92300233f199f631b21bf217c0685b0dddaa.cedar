forbid(
  principal in a::"\0\0",
  action in [Action::"action",Action::"action"],
  resource in a::"\0\0"
) when {
  (true && ("" like "")) && ("" like "")
};

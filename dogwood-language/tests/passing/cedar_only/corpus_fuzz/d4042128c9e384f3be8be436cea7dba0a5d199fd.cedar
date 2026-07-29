forbid(
  principal in a::"\0\0\0",
  action in [Action::"action",Action::"action"],
  resource is a in a::"\0\0\0"
) when {
  (true && ("" like "")) && ("" like "")
};

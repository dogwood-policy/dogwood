permit(
  principal in a::"\0\0\0\0",
  action in [Action::"action"],
  resource in a::"\0\0\0\0"
) when {
  (true && ((if ("" like "......") then "\0\0\0\0\0\0\0" else "\0\0\0\0\0\0\0\0\0\0\0\0\0") like "\0\0\0\0\0\0")) && false
};

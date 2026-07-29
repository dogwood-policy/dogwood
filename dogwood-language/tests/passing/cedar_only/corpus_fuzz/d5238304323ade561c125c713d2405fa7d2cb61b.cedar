permit(
  principal,
  action == Action::"action",
  resource == a::"\0\0\0\0\0@"
) when {
  true && ((if ("袋." like "**") then (principal in action) else false) || (false || ((ip("00.255.91.59")).isLoopback())))
};

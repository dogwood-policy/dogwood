permit(
  principal == a::"\0\0\0",
  action == Action::"action",
  resource is a in a::"\0\0\0"
) when {
  true && (((!((duration("27418944067617790m")) <= (duration("0ms")))) || false) || false)
};

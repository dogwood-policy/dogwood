permit(
  principal,
  action == Action::"action",
  resource in a::"@\0"
) when {
  (true && ({"": (datetime("0000-01-01")).offset(duration("0ms"))} has "")) && false
};

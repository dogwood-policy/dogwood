permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && ((if ("" like "") then ["", ""] else ["a\0\0\0\0\u{2}", ""]).containsAny([(datetime("0000-01-01")).offset(duration("0ms")), datetime("0000-01-01")]))) && false) && false
};

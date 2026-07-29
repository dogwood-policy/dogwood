permit(
  principal == Pm::"\0\0\0\u{5}",
  action in [Action::""],
  resource in g3::"\0\0\0\0"
) when {
  (true && (principal has "d23\u{4}")) && false
};

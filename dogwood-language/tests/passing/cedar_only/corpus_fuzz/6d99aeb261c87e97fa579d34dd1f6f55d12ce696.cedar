permit(
  principal,
  action == Action::"action",
  resource
) when {
  true && ([{"": []}[""], if false then [false] else []].containsAny([[true, false], [true, true, false], []]))
};

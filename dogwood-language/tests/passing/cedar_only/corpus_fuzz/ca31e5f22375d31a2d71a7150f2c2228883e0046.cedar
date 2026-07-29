permit(
  principal,
  action == Action::"action",
  resource == a::"\n"
) when {
  ((true && ([[action], [action, action, action], []].containsAny([[false, false], [false, false, false]]))) && false) && false
};

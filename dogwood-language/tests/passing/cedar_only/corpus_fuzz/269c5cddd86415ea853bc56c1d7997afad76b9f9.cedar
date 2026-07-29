permit(
  principal,
  action == Action::"action",
  resource == a::"\n"
) when {
  ((true && ([[action], [action], [principal]].containsAny([[true, false], [], []]))) && false) && false
};

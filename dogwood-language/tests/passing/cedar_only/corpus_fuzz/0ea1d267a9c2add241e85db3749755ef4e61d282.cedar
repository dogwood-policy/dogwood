forbid(
  principal == a::"\n",
  action == Action::"action",
  resource == a::"\n"
) when {
  ((true && ([[action], [action], [action]].containsAny([[], [], [[], []]]))) && false) && false
};

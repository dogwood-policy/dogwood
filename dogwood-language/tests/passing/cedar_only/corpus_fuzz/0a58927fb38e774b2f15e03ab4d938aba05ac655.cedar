forbid(
  principal,
  action in [Action::"action"],
  resource == a::""
) when {
  (true && (!false)) && ({"": action is a}[""])
};

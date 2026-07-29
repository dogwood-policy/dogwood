permit(
  principal is a in a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource is a in a::""
) when {
  ((true && ([true, false, true] == [true, false, false])) && true) && false
};

permit(
  principal == a::"",
  action in [Action::"action"],
  resource is a in a::" \0"
) when {
  ((true && (context == false)) && false) && false
};

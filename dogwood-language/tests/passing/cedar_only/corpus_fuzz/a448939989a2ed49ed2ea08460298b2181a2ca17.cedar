permit(
  principal in a::"",
  action in [Action::"action"],
  resource
) when {
  ((true && ("" like "")) && false) && true
};

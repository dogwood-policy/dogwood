@Wj000000("")
permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (principal in a::"")) && true) && true
};

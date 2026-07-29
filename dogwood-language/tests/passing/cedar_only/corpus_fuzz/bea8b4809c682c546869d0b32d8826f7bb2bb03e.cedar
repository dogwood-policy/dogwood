@fbb000000000000("")
permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (action in a::"")) && false) && true
};

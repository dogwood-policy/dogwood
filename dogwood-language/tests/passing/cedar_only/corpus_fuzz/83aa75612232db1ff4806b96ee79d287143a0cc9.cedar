@LRw0000000000000("")
permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && (false || (false || (action in principal)))
};

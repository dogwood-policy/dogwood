@A00000000000("")
permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (if true then false else true)) && true) && true
};

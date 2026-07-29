@A00000000000("")
permit(
  principal,
  action == Action::"action",
  resource
) when {
  (true && (a::"" in [action, action, action])) && true
};

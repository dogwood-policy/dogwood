permit(
  principal in a::"",
  action == Action::"action",
  resource
) when {
  (true && (resource in resource)) && false
};

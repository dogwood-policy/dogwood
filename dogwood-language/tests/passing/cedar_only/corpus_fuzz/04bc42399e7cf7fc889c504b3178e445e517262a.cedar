permit(
  principal,
  action == Action::"action",
  resource
) when {
  (true && (action in [{"": resource}[""], a::"", {"": action}[""]])) && (resource in [action, a::""])
};

permit(
  principal,
  action == Action::"action",
  resource
) when {
  (true && (action in [{"": action}[""], {"": action}[""], {"": action}[""]])) && (({"": resource}[""]) in [resource, resource])
};

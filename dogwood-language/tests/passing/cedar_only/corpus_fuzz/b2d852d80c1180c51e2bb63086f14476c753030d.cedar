permit(
  principal is a in a::"",
  action == Action::":",
  resource is a
) when {
  true && (resource in a::"")
};

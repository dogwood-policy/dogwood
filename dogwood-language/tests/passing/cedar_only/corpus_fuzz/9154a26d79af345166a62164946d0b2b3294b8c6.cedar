@g("")
permit(
  principal in a::"",
  action in [Action::":"],
  resource is a
) when {
  true && (({"": action}[""]) in resource)
};

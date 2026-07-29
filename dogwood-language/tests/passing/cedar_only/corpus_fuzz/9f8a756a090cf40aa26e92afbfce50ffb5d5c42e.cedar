permit(
  principal == a::"",
  action in [Action::":~"],
  resource is a in a::""
) when {
  true
};

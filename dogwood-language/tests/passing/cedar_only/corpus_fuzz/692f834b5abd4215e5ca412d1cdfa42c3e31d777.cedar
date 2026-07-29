permit(
  principal == a::"",
  action in [Action::":"],
  resource == a::""
) when {
  true && ("" like "")
};

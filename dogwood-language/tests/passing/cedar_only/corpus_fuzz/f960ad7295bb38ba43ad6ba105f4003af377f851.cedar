permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource is a
) when {
  true && ((a::"" in a::"\u{2}") || (context["%\u{2}"]))
};

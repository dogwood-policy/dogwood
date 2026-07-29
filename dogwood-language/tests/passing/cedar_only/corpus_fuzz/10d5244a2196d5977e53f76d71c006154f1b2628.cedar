permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource is a
) when {
  true && ((a::"" in a::"\u{2}") || ((if true then context else context)["%\u{2}"]))
};

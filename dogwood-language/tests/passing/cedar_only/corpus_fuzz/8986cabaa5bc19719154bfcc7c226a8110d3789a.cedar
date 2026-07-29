permit(
  principal,
  action in [Action::"action"],
  resource in a::"\u{1} "
) when {
  true && (!((context[""]) like ""))
};

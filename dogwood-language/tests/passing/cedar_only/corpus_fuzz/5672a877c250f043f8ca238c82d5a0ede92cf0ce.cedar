permit(
  principal,
  action in [Action::"action"],
  resource in a::"\0\0"
) when {
  true && (!((context[""]) like "莎*"))
};

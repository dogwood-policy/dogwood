forbid(
  principal in a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && ((if ([[context, context], [context]].containsAny([])) then context else context)["\0"])) && false
};

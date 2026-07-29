forbid(
  principal in a::"\0\0\0@\0",
  action in [Action::"action"],
  resource in a::"\0\0\0@\0"
) when {
  (true && ((if ([[context, context], [context, context, context]].containsAny([duration("39860172908331435h698513293311ms"), duration("0ms")])) then context else context)["\0"])) && false
};

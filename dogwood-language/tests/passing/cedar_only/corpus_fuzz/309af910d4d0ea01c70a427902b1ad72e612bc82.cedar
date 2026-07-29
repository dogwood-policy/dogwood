forbid(
  principal in a::"\01\0",
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::"\01\0"
) when {
  (true && ((if ([[context, context], []].containsAny([[resource, resource], [principal, principal]])) then context else context)["\0"])) && false
};

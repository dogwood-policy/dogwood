forbid(
  principal in a::"\u{b2cf2}\u{2}\0\0\0",
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::"\u{b2cf2}\u{2}\0\0\0"
) when {
  (true && ((if ([[context, context], []].containsAny([[resource, action], [resource, resource]])) then {"\0": false} else {"\0": false})["\0"])) && false
};

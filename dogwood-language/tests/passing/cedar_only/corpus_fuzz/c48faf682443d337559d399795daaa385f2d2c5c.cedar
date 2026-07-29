forbid(
  principal in a::"\u{b2cf2}\u{2}\0\0\0",
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && ((if ([[resource, principal], [], []].containsAny([[resource, a::"\u{b2cf2}\u{2}\0\0\0"], [principal, principal, principal]])) then {"\0": false} else {"\0": false})["\0"])) && (resource in resource)
};

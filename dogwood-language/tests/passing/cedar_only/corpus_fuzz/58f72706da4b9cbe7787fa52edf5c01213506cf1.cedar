forbid(
  principal in a::"\u{b2cf2}\u{2}\0\0\0",
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && ((if ([[context, context], []].containsAny([[], [resource, resource]])) then (if false then {"\0": false} else {"\0": false}) else (if false then {"\0": false} else {"\0": true}))["\0"])) && (((ip("\u{f}")).isIpv6()) || false)
};

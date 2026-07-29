forbid(
  principal in a::"",
  action in [Action::"action"],
  resource in a::"\u{b2cf2}\u{2}\0\0\0"
) when {
  (true && ((if ([[false, false], []].containsAny([[resource, resource], [resource, resource]])) then ({"": {"\0": true}}[""]) else ({"": {"\0": true}}[""]))["\0"])) && ("U" like "")
};

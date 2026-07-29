forbid(
  principal in a::"\u{b2cf2}\u{2}\0\0",
  action in [Action::"action"],
  resource
) when {
  (true && ((if ([[context, context], []].containsAny([[{}, {}], [{}, {}]])) then (if false then [[context, context], [{"\0\0\0\0": [resource, resource]}, context]] else []) else (if false then [[{"\0\0\0\0": [principal, principal]}, context, {"\0\0\0\0": [action, principal]}], []] else [])).containsAny(if ([[context, context], []].containsAny([[{}, {}], [{}, {}]])) then [false, false] else [false, false]))) && false
};

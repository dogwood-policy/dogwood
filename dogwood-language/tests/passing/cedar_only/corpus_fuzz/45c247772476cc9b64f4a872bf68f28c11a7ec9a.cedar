forbid(
  principal in a::"\u{b2cf2}\u{2}\0\0\0",
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::"\u{b2cf2}\u{2}\0\0\0"
) when {
  (true && ({"": "" like ""}[""])) && ([{"": [{}, {}, context]}[""], []].containsAny(if ("" like "") then (if false then [[], []] else [[resource, a::"\u{b2cf2}\u{2}\0\0\0"], []]) else []))
};

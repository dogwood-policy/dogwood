forbid(
  principal is a,
  action in [Action::"action",Action::"action"],
  resource == a::"Ų"
) when {
  (true && ([[{"\0\0\0\0": []}, {"\0\0\0\0": []}], if false then [{"\0\0\0\0": [resource]}, {"\0\0\0\0": []}] else [], {"\u{1c}": [{"\0\0\0\0": [a::"\0\0\0\0\0\0\u{18}\0\0", principal, principal]}, context, {"\0\0\0\0": [resource, resource]}]}["\u{1c}"]].containsAny(if ("" like "") then (if false then [{}, {}] else [{}, {}]) else (if false then [{}, {}] else [{}, {}, context])))) && false
};

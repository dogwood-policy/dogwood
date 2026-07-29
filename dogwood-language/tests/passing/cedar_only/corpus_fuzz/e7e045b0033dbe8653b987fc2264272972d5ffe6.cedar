forbid(
  principal is a,
  action in [Action::"action",Action::"action"],
  resource == a::"Ų"
) when {
  (true && ((if ({} has "") then [[{"\0\0\0\0\0\0\u{7}an ": [principal, principal]}, context]] else [[{"\0\0\0\0\0\0\u{7}an ": [a::"Ų", principal, resource]}, {"\0\0\0\0\0\0\u{7}an ": [a::"Ų", principal, resource]}, {"\0\0\0\0\0\0\u{7}an ": [a::"\'\'", a::"\'\'\'\'\'\'\'\'\'", a::"\'\'\'\'\'"]}], [{"\0\0\0\0\0\0\u{7}an ": [a::"\'", a::"\'\'", action]}, {"\0\0\0\0\0\0\u{7}an ": [principal, resource, principal]}, context]]).containsAny([]))) && false
};

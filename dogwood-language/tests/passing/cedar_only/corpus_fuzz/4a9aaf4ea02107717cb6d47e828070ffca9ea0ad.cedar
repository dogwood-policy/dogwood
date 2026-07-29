forbid(
  principal is a,
  action in [Action::"action",Action::"action"],
  resource == a::"Ų"
) when {
  (true && ([[{"\0\0\0\0": []}, {"\0\0\0\0": []}], if false then [{"\0\0\0\0": [resource]}, context] else [{"\0\0\0\0": [a::"Ų", principal]}, {"\0\0\0\0": []}], if true then [{"\0\0\0\0": []}] else [{"\0\0\0\0": [a::"Ų", action]}]].containsAny([]))) && false
};

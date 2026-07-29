forbid(
  principal is a,
  action in [Action::"action",Action::"action"],
  resource == a::"Ų"
) when {
  (true && ([[{"\0\0\0\0": []}, {"\0\0\0\0": []}], if false then [{"\0\0\0\0": [resource]}, context] else [{"\0\0\0\0": [a::"", principal]}, context], []].containsAny([]))) && false
};

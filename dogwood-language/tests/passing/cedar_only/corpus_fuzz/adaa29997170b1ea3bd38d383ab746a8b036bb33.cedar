forbid(
  principal is a,
  action in [Action::"action",Action::"action"],
  resource == a::"Ų"
) when {
  (true && ([[{"\0\0\0\0": []}, {"\0\0\0\0": []}], if false then [{"\0\0\0\0": [resource]}, context] else [{"\0\0\0\0": [a::"Ų", principal, resource]}, context], if true then [{"\0\0\0\0": [principal, action]}, {"\0\0\0\0": [action, a::"Ų"]}, {"\0\0\0\0": [action, principal]}] else []].containsAny([]))) && false
};

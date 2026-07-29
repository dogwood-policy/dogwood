forbid(
  principal is a,
  action in [Action::"action",Action::"action"],
  resource == a::"Ų"
) when {
  (true && ([[{"\0\0\0\0": []}, {"\0\0\0\0": []}], if false then [{"\0\0\0\0": [resource]}, {"\0\0\0\0": [action, resource, principal]}] else [{"\0\0\0\0": [a::"Ų", action]}], [{"\0\0\0\0": []}, context]].containsAny([]))) && false
};

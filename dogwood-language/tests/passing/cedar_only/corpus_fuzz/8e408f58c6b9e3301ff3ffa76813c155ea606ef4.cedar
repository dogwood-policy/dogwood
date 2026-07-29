forbid(
  principal is a,
  action in [Action::"action",Action::"action"],
  resource == a::"Ų"
) when {
  (true && ([[context], [context, {"\0\0\0\0": []}, {"\0\0\0\0": [action, resource, principal]}], if true then [{"\0\0\0\0": [action, a::""]}, {"\0\0\0\0": [a::"", principal, principal]}, context] else []].containsAny([]))) && false
};

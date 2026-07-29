forbid(
  principal is a,
  action in [Action::"action",Action::"action"],
  resource == a::"Ų"
) when {
  (true && ((if false then ({U: []}.U) else (if true then [[context, {"\0\0\0\0\0": []}, {"\0\0\0\0\0": []}], [{"\0\0\0\0\0": [resource]}, context], [{"\0\0\0\0\0": [action, a::"Ų"]}]] else [[context, context]])).containsAny([]))) && false
};

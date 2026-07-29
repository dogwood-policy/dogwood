forbid(
  principal is a,
  action in [Action::"action",Action::"action"],
  resource == a::"Ų"
) when {
  (true && (((if false then {"": []} else {"": [[{"\0\0\0\0\0\0\u{7}an": []}], [{"\0\0\0\0\0\0\u{7}an": [a::"Ų", principal, resource]}, context], [{"\0\0\0\0\0\0\u{7}an": [principal]}, {"\0\0\0\0\0\0\u{7}an": [a::""]}]]})[""]).containsAny([datetime("5954-01-01"), datetime("0000-01-01")]))) && false
};

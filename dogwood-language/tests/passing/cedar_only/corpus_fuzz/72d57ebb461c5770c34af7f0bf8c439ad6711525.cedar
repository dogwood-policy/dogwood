forbid(
  principal in a::"",
  action in [Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && ([[[ip("138.138.138.138"), ip("214.138.138.138")], [ip("8a8a:8a8a:8a8a:8a8a:8a8a:8a8a:ffff:ffff"), ip("228.244.228.228"), ip("3f3f:3f3f:3f3f:33f:3f3f:3fff:5b99:990e/63")]], if true then [[ip("1f1f:1f1f:1f1f:1f1f:1f1f:1f1f:1f1f:1f1f/31"), ip("1f1f:1f1f:1f1f:1f1f:1f1f:1f1f:1f1f:1f1f/113"), ip("1f1f:1f1f:1f1f:1f1f:1f1f:1f1f:1f1f:1f1f/31")], [ip("5353:5353:5353:5353:5353:5353:5353:305b/83")], [ip("1f1f:1f1f:1f1f:1f1f:1f1f:1f1f:1f1f:1f1f/31"), ip("ed53:5353:14ff:2499:401d:33f:3f3f:3f3f/108"), ip("5353:5353:5353:5353:5353:5353:5353:5353/83")]] else []] == [])) && false
};

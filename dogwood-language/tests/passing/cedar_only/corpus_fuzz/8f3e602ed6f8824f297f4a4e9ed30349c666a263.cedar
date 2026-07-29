forbid(
  principal in a::"",
  action in [Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && ([[[ip("138.138.138.138"), ip("214.138.138.138")], [ip("8a8a:8a8a:8a8a:8a8a:8a8a:8a8a:ffff:ffff"), ip("228.244.228.228"), ip("3f3f:3f3f:3f3f:33f:3f3f:3fff:5b99:990e/63")]], if true then [[ip("1f1f:1f1f:1f1f:1f1f:1f1f:1f1f:1f1f:1f1f/31"), ip("31.0.0.0/31"), ip("7171:711f:1f1f:1f1f:1f1f:1f1f:1f1f:1f1f/113")], [ip("1f1f:1f1f:aaaa:aaaa:aaaa:aa0b:1f1f:1f1f/31"), ip("1f1f:1f1f:1f1f:1f1f:1f1f:1f1f:1f1f:1f1f/31"), ip("1f1f:1f1f:1f1f:1f1f:1f1f:1f3f:1f1f:1f1f/31")], []] else []] == [])) && false
};

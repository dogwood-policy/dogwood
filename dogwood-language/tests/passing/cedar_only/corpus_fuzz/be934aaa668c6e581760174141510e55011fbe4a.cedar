forbid(
  principal in a::"",
  action in [Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && ([[[ip("138.138.138.138"), ip("138.138.138.138")], [ip("0.206.206.2006/0"), ip("2206.206.206.206")]], [[ip("138.138.138.138"), ip("206.206.206.206")], []]] == [])) && false
};

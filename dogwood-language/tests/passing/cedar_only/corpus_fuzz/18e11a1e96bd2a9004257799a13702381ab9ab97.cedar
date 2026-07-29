forbid(
  principal in a::"",
  action in [Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && ([[[ip("138.138.138.138"), ip("206.206.206.200")], [ip("7.0.0.0"), ip("50.49.49.50")]], [[ip("0.0.0.0"), ip("0.0.0.0")], []]] == [])) && false
};

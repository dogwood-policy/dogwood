forbid(
  principal in a::"",
  action in [Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && ([[[ip("138.138.138.138"), ip("206.206.206.200")], [ip("0.0.64.0/88"), ip("206.206.207.206")]], []] == [])) && false
};

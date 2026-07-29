permit(
  principal,
  action in [Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && ([[[ip("138.138.138.138"), ip("64.153.37.0/17")], [ip("0.0.0.0"), ip("0.0.0.0")]], []] == [])) && false
};

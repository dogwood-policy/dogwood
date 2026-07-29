forbid(
  principal is a,
  action in [Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && ([[[ip("0.138.138.138/9"), ip("138.138.223.0")], [ip("::ff:ffff:ff2a:f9f0"), ip("0.0.0.0"), ip("0.0.0.0")]], []] == [])) && false
};

forbid(
  principal in a::"",
  action in [Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && ([[[ip("138.138.138.138"), ip("233.138.138.138")], [ip("99.65.255.65/"), ip("70:8a8a:828a:8a8a:8a00:2b:3636:3636")]], []] == [])) && false
};

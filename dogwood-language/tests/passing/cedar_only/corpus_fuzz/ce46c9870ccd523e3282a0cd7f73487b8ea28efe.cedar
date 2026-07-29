forbid(
  principal in a::"",
  action in [Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && (!([[ip("0.138.138.138"), ip("0.0.0.0")], []] == []))) && ([[[ip("62.62.62.62"), ip("62.62.62.62")], [ip("62.138.138.138"), ip("138.138.138.138")]], []] == [])
};

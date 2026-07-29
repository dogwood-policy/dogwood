forbid(
  principal in a::"",
  action in [Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && ([[[ip("65.255.65.0/200"), ip("239.104.239.239/0")], []], []] == [])) && false
};

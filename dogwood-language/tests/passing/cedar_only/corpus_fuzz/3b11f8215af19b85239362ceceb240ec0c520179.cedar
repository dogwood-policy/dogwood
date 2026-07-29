forbid(
  principal in a::"",
  action in [Action::"",Action::""],
  resource in a::""
) when {
  (true && ([[ip("99.65.255.65//8"), ip("::e706:ef")] == [], false] == [])) && false
};

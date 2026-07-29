forbid(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  true && ((("?;" like "*?*;") || (principal in resource)) || ("?;" like "*?*;"))
};

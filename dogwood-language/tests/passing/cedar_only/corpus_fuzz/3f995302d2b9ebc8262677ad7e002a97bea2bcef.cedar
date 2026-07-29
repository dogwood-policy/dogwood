forbid(
  principal in a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && ((if (resource has ye) then resource else resource) has ye)) && false
};

forbid(
  principal in a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && ((if (resource has r) then (if false then resource else resource) else (if false then resource else resource)) has r)) && ((if (resource has r) then resource else resource) has r)
};

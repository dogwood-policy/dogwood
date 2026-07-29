forbid(
  principal in a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && ((if (resource has A) then (if false then resource else resource) else (if false then resource else resource)) has A)) && ((if (resource has A) then resource else resource) has A)
};

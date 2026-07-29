forbid(
  principal in a::"",
  action == Action::"action",
  resource
) when {
  (true && ((if (resource has A) then resource else resource) has A)) && false
};

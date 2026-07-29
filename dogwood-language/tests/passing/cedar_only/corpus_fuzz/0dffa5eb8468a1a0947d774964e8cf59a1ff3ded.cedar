forbid(
  principal,
  action,
  resource in a::""
) when {
  ((true && ((if (resource has A) then (if true then resource else a::"") else action) has A)) && (action in action)) && (a::"" in (if (resource has A) then (if false then resource else resource) else resource))
};

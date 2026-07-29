forbid(
  principal,
  action,
  resource in a::""
) when {
  ((true && ((if (resource has A) then (if true then resource else principal) else (if false then resource else resource)) has A)) && (resource has A)) && false
};

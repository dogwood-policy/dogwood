permit(
  principal,
  action in [Action::"action",Action::"action"],
  resource in a::""
) when {
  (true && ([[resource, resource], [resource, resource]] == [[resource, resource], [resource, resource]])) && ((if false then [[[]]] else [[[ip("170.95.188.15"), ip("0.0.0.0")]], [], []]) == [])
};

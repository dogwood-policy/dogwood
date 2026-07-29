forbid(
  principal,
  action,
  resource == a::""
) when {
  (true && (resource in resource)) && (action in [action, action, resource])
};

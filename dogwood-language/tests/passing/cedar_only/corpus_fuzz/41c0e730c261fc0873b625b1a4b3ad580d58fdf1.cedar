forbid(
  principal,
  action,
  resource
) when {
  (true && ((resource in resource) == (action in [a::"", resource, resource]))) && false
};

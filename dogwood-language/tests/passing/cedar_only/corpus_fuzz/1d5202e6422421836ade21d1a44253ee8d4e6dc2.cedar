forbid(
  principal,
  action,
  resource
) when {
  (true && (resource in resource)) && (principal in a::"")
};

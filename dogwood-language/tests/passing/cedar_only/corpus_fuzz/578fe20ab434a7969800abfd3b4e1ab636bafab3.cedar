forbid(
  principal,
  action,
  resource
) when {
  (true && (resource has "")) && (principal is a)
};

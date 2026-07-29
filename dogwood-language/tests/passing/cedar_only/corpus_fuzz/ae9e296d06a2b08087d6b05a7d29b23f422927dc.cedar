forbid(
  principal,
  action,
  resource
) when {
  (true && (resource has "")) && true
};

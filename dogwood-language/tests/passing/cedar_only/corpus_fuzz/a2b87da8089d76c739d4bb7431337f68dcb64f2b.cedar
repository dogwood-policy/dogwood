forbid(
  principal,
  action,
  resource
) when {
  (true && (action in resource)) && false
};

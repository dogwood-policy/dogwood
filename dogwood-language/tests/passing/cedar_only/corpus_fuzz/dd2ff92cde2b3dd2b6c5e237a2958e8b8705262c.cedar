forbid(
  principal,
  action,
  resource
) when {
  (true && (action in action)) && (action in resource)
};

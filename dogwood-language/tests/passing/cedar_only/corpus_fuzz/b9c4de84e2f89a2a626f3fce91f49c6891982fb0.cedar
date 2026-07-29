forbid(
  principal,
  action in [M::Action::"action"],
  resource
) when {
  (true && (action in resource)) && false
};

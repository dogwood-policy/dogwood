permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  ((true && (if ((if false then (ip("0.0.0.0/0")) else (ip("0.0.0.0"))).isLoopback()) then false else false)) && false) && false
};

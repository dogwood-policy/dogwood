permit(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && ((ip("")).isInRange(if true then (if false then (ip("0.0.0.0")) else (ip("0.0.0.0"))) else (if false then (ip("0.0.0.0")) else (ip("0.0.0.0")))))
};

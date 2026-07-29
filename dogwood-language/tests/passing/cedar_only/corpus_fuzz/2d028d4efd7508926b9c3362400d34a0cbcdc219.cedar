permit(
  principal is a,
  action in [Action::"action"],
  resource == a::""
) when {
  true && ((if false then (if false then (ip("0.0.0.0")) else (ip("0.0.0.0"))) else (if false then (ip("::")) else (ip("0.0.0.0")))).isInRange(if false then (if false then (ip("0.0.0.0")) else (ip("0.0.0.0"))) else (ip("")), if false then (if false then (ip("0.0.0.0")) else (ip("0.0.0.0"))) else (if false then (ip("0.0.0.0")) else (ip("0.0.0.0"))), if false then (if false then (ip("0.0.0.0")) else (ip("0.0.0.0"))) else (if false then (ip("0.0.0.0")) else (ip("0.0.0.0"))), ip("0.0.0.0")))
};

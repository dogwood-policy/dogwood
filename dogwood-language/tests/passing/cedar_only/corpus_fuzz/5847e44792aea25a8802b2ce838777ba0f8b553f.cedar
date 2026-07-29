permit(
  principal is A::a,
  action in [A::Action::"action"],
  resource is A::a
) when {
  true && ((if false then (if false then (ip("0.0.0.0")) else (ip("0.0.0.0"))) else (if false then (ip("0.0.0.0")) else (ip("0.0.0.0")))).isInRange(if false then (if false then (ip("0.0.0.0")) else (ip("0.0.0.0"))) else (if false then (ip("54.54.129.101/1")) else (ip("0.0.0.0")))))
};

forbid(
  principal is jz::a,
  action == jz::Action::"action",
  resource == jz::a::">>>"
) when {
  true && (jz::a::">>>" in (if ((decimal("4488509071816718.7905")).lessThan(decimal("882550108624535.4106"))) then action else action))
};

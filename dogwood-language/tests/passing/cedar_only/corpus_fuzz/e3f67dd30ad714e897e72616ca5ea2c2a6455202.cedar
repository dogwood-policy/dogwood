forbid(
  principal is A::a,
  action in [A::Action::"action"],
  resource == A::a::""
) when {
  true
};

forbid(
  principal is A::A::a,
  action in [A::A::Action::"action"],
  resource == A::A::a::""
) when {
  true
};

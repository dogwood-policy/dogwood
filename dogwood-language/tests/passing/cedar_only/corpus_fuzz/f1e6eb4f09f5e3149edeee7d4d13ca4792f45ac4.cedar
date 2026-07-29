forbid(
  principal == A::a::"\0\0",
  action in [A::Action::"action"],
  resource == A::a::"\0\0"
) when {
  false
};

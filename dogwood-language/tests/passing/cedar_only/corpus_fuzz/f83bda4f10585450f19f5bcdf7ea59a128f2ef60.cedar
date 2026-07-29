forbid(
  principal is A::a in A::a::"\0\0Y",
  action in [A::Action::"action",A::Action::"action",A::Action::"action"],
  resource is A::a in A::a::"\0\0Y"
) when {
  true
};

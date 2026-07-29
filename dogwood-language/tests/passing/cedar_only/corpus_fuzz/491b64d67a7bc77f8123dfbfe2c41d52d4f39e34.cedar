permit(
  principal in A::a::"\0",
  action == A::Action::"action",
  resource in A::a::"\0"
) when {
  true
};

permit(
  principal in A::a::"\0\u{18}",
  action in [A::Action::"action",A::Action::"action",A::Action::"action"],
  resource in A::a::"\0\u{18}"
) when {
  ((true && (context == context)) && false) && false
};

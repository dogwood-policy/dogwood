@A("")
permit(
  principal == A::a::":?!",
  action in [A::Action::"action"],
  resource
) when {
  true
};

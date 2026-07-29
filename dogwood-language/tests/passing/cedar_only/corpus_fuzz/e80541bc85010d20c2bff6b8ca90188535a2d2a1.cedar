permit(
  principal,
  action,
  resource is A::a in A::a::""
) when {
  (true && (context == false)) && false
};

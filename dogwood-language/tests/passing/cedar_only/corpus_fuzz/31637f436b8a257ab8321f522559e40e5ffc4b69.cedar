@_lS00000000000("")
permit(
  principal,
  action in [Action::""],
  resource == a::""
) when {
  ((true && (principal in principal)) && ("\u{4}qq" like "q*q*q**q*q*q")) && true
};

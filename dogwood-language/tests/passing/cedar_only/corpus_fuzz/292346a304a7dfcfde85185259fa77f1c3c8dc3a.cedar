permit(
  principal in a::"",
  action,
  resource in a::""
) when {
  (true && (A::BF00000000000000::"" in principal)) && false
};

forbid(
  principal in a::"",
  action == Action::"action",
  resource in a::""
) when {
  true && ([].containsAny([ip("::e4e4:67e4:e4e4:676e"), ip("0.0.0.0")]))
};

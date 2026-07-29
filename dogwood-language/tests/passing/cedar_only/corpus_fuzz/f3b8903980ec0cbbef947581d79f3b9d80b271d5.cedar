forbid(
  principal is a in a::"**",
  action == Action::"action",
  resource
) when {
  true && ((duration("-0d0h0m0s")) <= (duration("9223372036854775808ms")))
};

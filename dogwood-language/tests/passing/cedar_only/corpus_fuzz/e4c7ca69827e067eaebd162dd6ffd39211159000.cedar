permit(
  principal,
  action in [Action::""],
  resource is a in a::""
) when {
  true && (if ([duration("1d1s9223372036854775807ms"), duration("1ms")].containsAll([])) then false else false)
};

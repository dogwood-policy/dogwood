permit(
  principal == a::"\0\0an r",
  action in [Action::"action"],
  resource in a::"\0\0an r"
) when {
  (true && ((ip(if false then "*0" else "")).isIpv6())) && ((action.r) has "xxpxx\u{e}\u{e}\u{e}\u{e}\u{e}\u{e}\u{e}\u{e}")
};

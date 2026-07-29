permit(
  principal is a in a::"\u{e}\u{e}\0",
  action == Action::"p",
  resource
) when {
  ((true && ((ip(if false then "" else "")).isMulticast())) && ((false && (principal in principal)) && false)) && false
};

@A("")
permit(
  principal == a::"\u{16}\u{16}\u{16}\u{16}\u{16}\u{16}\u{16}\u{16}\u{16}",
  action == Action::"action",
  resource == a::"\u{16}"
) when {
  false
};

permit(
  principal == a::"\u{2}",
  action == Action::"action",
  resource == a::"\u{2}"
) when {
  true && ([[false, true]].containsAll({"\u{e}.\u{e}\u{e}\u{e}": [decimal("-922337203685477.5808")]}["\u{e}.\u{e}\u{e}\u{e}"]))
};

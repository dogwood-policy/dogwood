@A000("")
permit(
  principal,
  action == Action::"action",
  resource in a::""
) when {
  (true && ((if ([] == []) then context else {"\u{2}": true})["\u{2}"])) && false
};

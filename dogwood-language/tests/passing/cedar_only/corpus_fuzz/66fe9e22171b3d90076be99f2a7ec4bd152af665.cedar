permit(
  principal,
  action == Action::"action",
  resource in a::""
) when {
  (true && (((if false then {"": ["", ""]} else {"": ["", "", ""]})[""]).containsAny([[], [false, false], [false, false, false]]))) && false
};

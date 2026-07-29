permit(
  principal,
  action == Action::"action",
  resource in a::""
) when {
  (true && (({"": ["", "3\u{18}", ""]}[""]).containsAny([false, false]))) && false
};

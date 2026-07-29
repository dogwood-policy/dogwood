permit(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  true && (["z\u{13}A\0\0\0", "", ""].containsAny([]))
};

permit(
  principal,
  action in [Action::"",Action::""],
  resource in a::""
) when {
  (true && (["", ""].containsAny([]))) && false
};

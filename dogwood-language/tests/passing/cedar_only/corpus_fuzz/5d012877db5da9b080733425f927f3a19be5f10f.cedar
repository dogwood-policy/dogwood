permit(
  principal == a::"",
  action in [Action::"",Action::"",Action::""],
  resource is a in a::"\u{6}"
) when {
  (true && (([true, false].contains(false)) || false)) && false
};

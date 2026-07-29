permit(
  principal == a::"",
  action == Action::"action",
  resource == a::"\0\0"
) when {
  (true && ([].containsAny([{}]))) && (action in [action, action, action])
};

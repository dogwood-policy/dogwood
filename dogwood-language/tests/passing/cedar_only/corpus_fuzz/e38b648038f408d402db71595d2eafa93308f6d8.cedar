permit(
  principal == a::"",
  action == Action::"action",
  resource == a::"e"
) when {
  true && (a::"e".q)
};

@S8200000000000("")
permit(
  principal,
  action == Action::"action",
  resource == a::""
) when {
  (true && (([] == []) == false)) && true
};

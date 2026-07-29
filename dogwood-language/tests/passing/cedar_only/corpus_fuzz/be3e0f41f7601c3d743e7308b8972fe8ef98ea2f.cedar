@P_W02000gkc3("$")
@r("")
forbid(
  principal == a::"R",
  action == Action::"action",
  resource == a::"R"
) when {
  true && (a::"R".r)
};

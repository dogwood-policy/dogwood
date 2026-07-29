@P_W("")
forbid(
  principal == a::"R",
  action == Action::"action",
  resource == a::""
) when {
  true && (a::"R".r)
};

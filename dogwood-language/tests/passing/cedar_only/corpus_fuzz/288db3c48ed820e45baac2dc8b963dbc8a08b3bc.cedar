@P_W02000gkc3("")
forbid(
  principal == a::"",
  action == Action::"action",
  resource == a::"R"
) when {
  true && (a::"R".r)
};

forbid(
  principal in a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && (a::"" in principal)) && (principal in a::"")
};

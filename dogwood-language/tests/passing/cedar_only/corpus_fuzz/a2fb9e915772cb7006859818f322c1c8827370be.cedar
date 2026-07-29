@Qdeddd00("")
forbid(
  principal in a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource == a::""
) when {
  (true && (a::"" == principal)) && (a::"" is a)
};

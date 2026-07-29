@A00000000("")
@Y4m("")
forbid(
  principal in a::"R",
  action == Action::"action",
  resource == a::"R"
) when {
  (true && ((resource.r) || (resource.r))) && (action.r)
};

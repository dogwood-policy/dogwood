@X3333333000("")
forbid(
  principal in a::"R",
  action == Action::"action",
  resource == a::"R"
) when {
  true && ((if (action.r) then (action.r) else (action.r)) || (resource.r))
};

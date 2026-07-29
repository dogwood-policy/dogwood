permit(
  principal in a::"",
  action in [Action::"action"],
  resource is a
) when {
  (true && ("?a" like "*?*a")) && (if ("?a" like "*") then (("?a" like "*?*a") && ("?a" like "*?*a")) else false)
};

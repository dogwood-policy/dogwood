permit(
  principal in a::"",
  action in [Action::"action"],
  resource is a
) when {
  (true && ("?a" like "*?*a")) && (if ("?a" like "*?*a") then ("?a" like "*?*a") else ("?a" like "*?*a"))
};

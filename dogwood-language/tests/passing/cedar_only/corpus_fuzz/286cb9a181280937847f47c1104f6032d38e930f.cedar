permit(
  principal in a::"",
  action in [Action::"action"],
  resource is a
) when {
  (true && ((if ("?a" like "*?*a") then {} else {}) has "?a")) && false
};

permit(
  principal in g3::"~",
  action in [Action::"action"],
  resource
) when {
  (true && ((if (action in g3::"~") then "" else (resource.getTag(""))) like "")) && ((if ("qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq" like "*qqqqq") then context else context)[""])
};

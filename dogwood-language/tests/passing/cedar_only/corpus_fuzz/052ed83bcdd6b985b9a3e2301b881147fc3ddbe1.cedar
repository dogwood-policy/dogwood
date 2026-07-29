permit(
  principal == r::"\0",
  action in [Action::"action"],
  resource
) when {
  true && ((if ([(datetime("1565-12-31T10:29:04Z")).offset(duration("-144115188075855873d32553086831936614335h980265857716006189m7306356827121451008ms"))].isEmpty()) then [] else []).isEmpty())
};

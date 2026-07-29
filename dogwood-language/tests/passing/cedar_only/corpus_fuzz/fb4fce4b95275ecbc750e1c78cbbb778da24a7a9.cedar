permit(
  principal == r::"\0",
  action in [Action::"action"],
  resource
) when {
  true && ((if ([(datetime("1565-12-31T21:45:35-0429")).offset(duration("-2199023255553d3255307777727266815h792648492087155355m"))].isEmpty()) then [] else []).isEmpty())
};

@tjjjjTSSS0p3("")
@zW("IE3-")
permit(
  principal == r::"",
  action in [Action::"action"],
  resource
) when {
  true && ((if ([(datetime("1565-12-31T21:45:35-0429")).offset(duration("-2199032555533255307777727266815h792803523226635675m"))].isEmpty()) then [] else [datetime("1914-02-01")]).isEmpty())
};

permit(
  principal == r::"",
  action in [Action::"action"],
  resource
) when {
  true && ((if ([(datetime("1565-12-31T10:34:13Z")).offset(duration("-231802921997011d1h3255307781250482175m3829163506703149s7306356827121451008ms"))].isEmpty()) then [] else [datetime("5654-11-23T22:22:22-0722"), datetime("7476-09-07")]).isEmpty())
};

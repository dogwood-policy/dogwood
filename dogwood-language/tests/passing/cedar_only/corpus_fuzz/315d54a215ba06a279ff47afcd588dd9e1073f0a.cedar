permit(
  principal == r::"\0",
  action in [Action::"action"],
  resource
) when {
  true && ((if ([(datetime("1565-12-31T10:34:13Z")).offset(duration("-1d432344464715939841h"))].isEmpty()) then ({"": [datetime("5746-11-24T10:58:22Z"), datetime("0000-01-01")]}[""]) else []).isEmpty())
};

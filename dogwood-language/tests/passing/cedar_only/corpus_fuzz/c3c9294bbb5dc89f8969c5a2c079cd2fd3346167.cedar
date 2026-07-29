permit(
  principal == r::"",
  action in [Action::"action"],
  resource
) when {
  true && ((if ([(datetime("1565-12-31T21:45:35-0429")).offset(duration("-2199023255553d3255307777727266815h794055866970708635m"))].isEmpty()) then (if true then [(datetime("1799-08-08T07:07:07.799+0707")).offset(duration("73063574556645743974ms")), datetime("5954-10-31T15:13:15.535+0045"), datetime("0000-01-01")] else []) else []).isEmpty())
};

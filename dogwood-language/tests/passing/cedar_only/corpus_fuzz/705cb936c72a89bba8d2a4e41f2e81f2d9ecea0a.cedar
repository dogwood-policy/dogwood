permit(
  principal,
  action,
  resource
) when {
  true && ((([ip("0:4169:f00:2000::100:0")].containsAny([duration("0ms")])) || false) && false)
};

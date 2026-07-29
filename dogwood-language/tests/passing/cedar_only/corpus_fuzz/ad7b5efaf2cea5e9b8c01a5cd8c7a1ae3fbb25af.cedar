forbid(
  principal,
  action,
  resource is a in a::""
) when {
  ((true && ([] == context)) && false) && false
};

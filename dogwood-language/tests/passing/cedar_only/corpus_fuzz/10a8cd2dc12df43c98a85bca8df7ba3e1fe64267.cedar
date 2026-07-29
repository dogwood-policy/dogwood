forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  true && (((datetime("2013-01-01")).offset(duration("0ms"))) == (datetime("0000-01-01")))
};

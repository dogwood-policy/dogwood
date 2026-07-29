forbid(
  principal is a,
  action == Action::"action",
  resource in a::""
) when {
  true && ([true].containsAny([(datetime("7242-11-14T10:46:46-0146")).toTime(), (datetime("7242-11-14T10:46:46-0150")).toTime()]))
};

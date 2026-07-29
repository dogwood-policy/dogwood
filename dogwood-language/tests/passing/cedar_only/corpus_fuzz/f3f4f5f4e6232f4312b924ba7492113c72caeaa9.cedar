forbid(
  principal == a::"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0[\u{1d}",
  action,
  resource is a
) when {
  true
};

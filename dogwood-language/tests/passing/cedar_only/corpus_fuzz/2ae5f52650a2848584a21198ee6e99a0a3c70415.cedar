forbid(
  principal == a::"@",
  action in [Action::"action"],
  resource
) when {
  true && ((!((ip("0.0.29.0")).isInRange(ip("ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff/126"), ip("62.62.62.62"), ip("62.62.62.62")))) || (!((ip("0.688.79.148")).isMulticast())))
};

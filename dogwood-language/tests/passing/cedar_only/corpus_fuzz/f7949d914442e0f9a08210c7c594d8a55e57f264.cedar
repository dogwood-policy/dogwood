forbid(
  principal == a::"..",
  action in [Action::"action"],
  resource
) when {
  true && ((!((ip("0.0.29.0")).isInRange(ip("62.62.62.62")))) || (!(false == false)))
};

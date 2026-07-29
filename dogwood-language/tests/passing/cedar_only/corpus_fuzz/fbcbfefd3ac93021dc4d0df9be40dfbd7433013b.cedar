forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  true && ((!((ip("0.0.29.0")).isInRange(ip("3e3e:3e3e:0:800:9::")))) || false)
};

forbid(
  principal == a::"@\u{e}",
  action in [Action::"action"],
  resource
) when {
  true && ((!((ip("0.0.29.0")).isInRange(ip("3e3e:3e3e:3e3e:3e3e:3e3e:3e3e:3e:3e00")))) || false)
};

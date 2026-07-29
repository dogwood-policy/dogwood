forbid(
  principal in a::"\0\0\0",
  action in [Action::"action",Action::"action"],
  resource in a::"\0\0\0"
) when {
  (true && ([[[[ip("303:303:303:303:303:303:303:303/3"), ip("303:362:ffff:ffff:303:303:303:303/3"), ip("101:101:101:5a01:101:101:101:101/1")], [ip("303:303:303:303:303:303:303:303/3"), ip("0.0.0.0"), ip("0.0.0.0")], []], [], []], [], []].containsAny([]))) && false
};

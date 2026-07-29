forbid(
  principal in a::" \0\0\0",
  action == Action::"action",
  resource in a::" \0\0\0"
) when {
  (true && ([(ip("24ff:2c5c:1b99:ffff:5c:5c5c:32ff:5c5c")).isIpv4(), true, (ip("::74ff:ff5c:4856:24ff:2c5c")).isIpv4()].containsAny([]))) && false
};

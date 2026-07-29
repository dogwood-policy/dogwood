forbid(
  principal == a::"D\0\0\0\u{10}kkkkkkkkk",
  action == Action::"action",
  resource is a in a::"D\0\0\0\u{10}kkkkkkkkk"
) when {
  true
};

@d("")
forbid(
  principal in a::"\0\0\u{6}",
  action in [Action::"",Action::""],
  resource in a::"\0\0\u{6}"
) when {
  ((true && (a::"\0\0\u{6}" has "\0\0\0\0\0\0\0\0\u{3}dd\0\0\0\0\0\0\0\0\0\0\0\0\0")) && false) && (a::"\0\0\u{6}" in a::"\0\0\u{6}")
};

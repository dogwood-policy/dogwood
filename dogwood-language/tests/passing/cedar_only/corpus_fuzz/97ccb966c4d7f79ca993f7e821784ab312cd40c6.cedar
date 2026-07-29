forbid(
  principal in a::"",
  action == Action::"action",
  resource == a::""
) when {
  (true && ((if (a::"\'\'\'\'\'\'\'\'\'\'\'\'\'" in [a::"\'\'r", principal, action]) then {"\n\nin\u{3}\0\0\0\0\0\0\0g": "\u{1}"} else context) == context)) && false
};

forbid(
  principal in a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::"\u{b2cf2}\u{2}\0\0\0"
) when {
  (true && ((if ([[context, context], []].containsAny([ip("178.178.178.178"), ip("5502:f41:1cf\u{2}:550f:b200:b200:b200:5502/125")])) then {"\0": false} else {"\0": false})["\0"])) && false
};

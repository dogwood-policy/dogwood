forbid(
  principal in A::a::"",
  action == A::Action::"action",
  resource in A::a::""
) when {
  (true && ((({"": {"": [ip("cbcb:cbcb:cbcb:cbcb:cbcb:cbcb:cbcb:cbcb/74"), ip("cbcb:cbcb:cbcb:cbcb:cbcb:cbff:ffff:ff00/74"), ip("82.82.82.82")]}}[""])[""]).containsAny((if false then context else {"\0\u{7f}\0": [ip("ffff:ffff:0:85:da00:7ff2:f200:d3f"), ip("0.0.0.0"), ip("0.0.0.0")]})["\0\u{7f}\0"]))) && false
};

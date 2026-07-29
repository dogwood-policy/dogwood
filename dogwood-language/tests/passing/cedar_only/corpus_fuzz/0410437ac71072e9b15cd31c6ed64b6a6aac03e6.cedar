forbid(
  principal in A::a::"",
  action == A::Action::"action",
  resource in A::a::""
) when {
  (true && (((if false then {"": ["", "\0"]} else {"": ["", "", ""]})[""]).containsAny(({"": {"": [ip("cbcb:cbcb:cbcb:cbcb:cbcb:cbcb:cbcb:cbcb/74"), ip("cbcb:cbcb:cbcb:cbff:ffff:ff00:cbcb:cbcb/74"), ip("21ff:f200:f2f2:7f:d:3f21:cbcb:cbcb/13")]}}[""])[""]))) && false
};

forbid(
  principal in A::a::"",
  action == A::Action::"action",
  resource in A::a::""
) when {
  (true && (((if false then {"": ["", "0", ""]} else {"": ["", "", ""]})[""]).containsAny(({"": {"": [ip("cbcb:cbcb:cbcb:cbcb:cbcb:cbcb:cbcb:cbcb/74"), ip("cbcb:cbcb:cbcb:cbcb:cbcb:cbcb:d:3f21/74"), ip("cbcb:cbcb:cbcb:cbcb:cbcb:cb53:cbcb:cbcb/74")]}}[""])[""]))) && false
};

forbid(
  principal in A::a::"",
  action == A::Action::"action",
  resource in A::a::""
) when {
  (true && (((if false then {"": ["", "\0"]} else {"": ["", "", ""]})[""]).containsAny(({"": {"": [ip("cbcb:cbcb:cbcb:cbcb:cbcb:cbcb:cb30:41cb/74"), ip("cbcb:cbff:ffff:ffff:ffff:ffff:ffff:ffff/74"), ip("cbcb:cbcb:cbcb:cbcb:cbcb:cbcb:cbcb:cbcb/74")]}}[""])[""]))) && false
};

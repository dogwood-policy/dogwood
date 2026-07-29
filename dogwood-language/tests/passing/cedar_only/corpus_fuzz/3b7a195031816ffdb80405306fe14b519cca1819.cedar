permit(
  principal in A::a::"",
  action == A::Action::"action",
  resource in A::a::""
) when {
  (true && (((if false then {"": ["\0", ""]} else {"": ["", "", ""]})[""]).containsAny(({"": {"": [ip("cbcb:cbcb:cbcb:cbcb:cbcb:cbcb:cbcb:cbcb/74"), ip("cbcb:cbcb:cbcb:cbcb:cbcb:cbcb:cbcb:cbcb/74"), ip("cbcb:cbcb:cbcb:cbcb:cbcb:cbcb:cbcb:cb32/74")]}}[""])[""]))) && false
};

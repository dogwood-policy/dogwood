forbid(
  principal in A::a::"",
  action == A::Action::"action",
  resource in A::a::""
) when {
  (true && (((if false then {"": ["", "\0"]} else {"": ["", "", ""]})[""]).containsAny(({"": {"": [ip("cbcb:cbcb:cb1a:1acb:cbcb:cbcb:cb35:41cb/74"), ip("cbcb:cbcb:7200:1:cbcb:cbcb:cbcb:4bcb/74"), ip("cbcb:cbcb:cbcb:cbcb:cbcb:cbcb:cbcb:cbcb")]}}[""])[""]))) && false
};

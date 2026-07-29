forbid(
  principal in a::"\0\0\0\0\0\0\0\0\0\0",
  action == Action::"action",
  resource in a::"\0\0\0\0\0\0\0\0\0\0"
) when {
  (true && (((if false then {"": ["\0", ""]} else {"": ["", "", ""]})[""]).containsAny(({"": {"": [ip("cbcb:cbcb:cbcb:cbcb:cbcb:cbcb:cbcb:cbcb/74"), ip("cbcb:cbcb:cbcb:cbcb:cbcb:ccb:cbcb:cbcb/74"), ip("0.0.0.0")]}}[""])[""]))) && (a::"\0\0\0\0\0\0\0\0\0\0" in a::"\0\0\0\0\0\0\0\0\0\0")
};

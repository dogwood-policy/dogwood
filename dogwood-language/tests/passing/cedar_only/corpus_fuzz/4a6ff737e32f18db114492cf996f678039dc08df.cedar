forbid(
  principal in A::a::"",
  action == A::Action::"action",
  resource in A::a::""
) when {
  (true && (((if false then {"": ["", "\0"]} else {"": ["", "", ""]})[""]).containsAny(({"": {"": [ip("f2f2:f2f2:f2f2:f252:797e:cbcb:cbcb:cbcb"), ip("8888:8888:88a9:0:cb:cbcb:cbcb:cbcb"), ip("85da:647f:f2f2:d:3f21:fff2:f2:f200")]}}[""])[""]))) && false
};

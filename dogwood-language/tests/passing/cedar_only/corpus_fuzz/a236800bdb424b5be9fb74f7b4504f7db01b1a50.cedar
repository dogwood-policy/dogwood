forbid(
  principal == A::a::"",
  action == A::Action::"action",
  resource in A::a::""
) when {
  (true && (((if false then {"": ["", ""]} else {"": ["\0", ""]})[""]).containsAny(["!~", "", ""]))) && false
};

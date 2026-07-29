forbid(
  principal in A::a::"",
  action == A::Action::"action",
  resource in A::a::""
) when {
  (true && (((if false then {"": ["\0", ""]} else {"": ["!", "?\r\0", "\u{7f}\0"]})[""]).containsAny((if true then {"\0": ["\u{1d}\0\u{7f}\0", "", ""]} else {"\0": ["", "", ""]})["\0"]))) && true
};

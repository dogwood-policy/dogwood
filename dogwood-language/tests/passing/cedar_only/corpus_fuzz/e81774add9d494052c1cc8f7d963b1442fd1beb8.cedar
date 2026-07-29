forbid(
  principal in H::a::"\0\0",
  action == H::Action::"action",
  resource in H::a::"\0\0"
) when {
  (true && (((if true then {"\0g\0": ["\r\0\u{7f}\0", "", ""]} else {"\0g\0": ["yR", ""]})["\0g\0"]).containsAny((if false then {"": ["", ""]} else {"": ["", ""]})[""]))) && (((if false then context else {"": ["!?\r\0\u{7f}@", "", ""]})[""]).containsAny((if true then {"\0": ["\r\0", "", ""]} else {"\0": []})["\0"]))
};

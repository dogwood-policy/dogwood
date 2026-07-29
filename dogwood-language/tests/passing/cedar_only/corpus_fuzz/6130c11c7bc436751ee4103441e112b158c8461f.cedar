forbid(
  principal in a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && (((if false then {"": ["", ""]} else {"": ["", ""]})[""]).containsAny((if false then {"": ["", ""]} else {"": ["", ""]})[""]))) && (((if false then {"": ["", ""]} else {"": []})[""]).containsAny([["", ""].containsAny(["\u{e}", ""]), principal in principal]))
};

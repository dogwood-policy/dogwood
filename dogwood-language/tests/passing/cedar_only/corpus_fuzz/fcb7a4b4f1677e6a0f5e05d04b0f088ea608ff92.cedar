forbid(
  principal in a::"",
  action == Action::":p",
  resource in a::""
) when {
  (true && (((if false then {"": ["X", ""]} else {"": ["", ""]})[""]).containsAny((if false then {"": ["", ""]} else {"": ["", ""]})[""]))) && false
};

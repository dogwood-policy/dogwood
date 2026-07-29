forbid(
  principal in a::"",
  action == Action::":p",
  resource in a::""
) when {
  (true && (((if false then context else {"": ["", ""]})[""]).containsAny((if false then {"": ["", ""]} else {"": ["", ""]})[""]))) && (((if false then context else {"": ["ian ", ""]})[""]).containsAny((if false then {"": ["", ""]} else {"": ["", ""]})[""]))
};

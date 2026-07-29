@A("")
forbid(
  principal in a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && (((if false then {"": ["", ""]} else {"": ["", ""]})[""]).containsAny((if false then {"": ["", ""]} else {"": ["", ""]})[""]))) && (({"": ["%%"]}[""]).containsAny([action]))
};

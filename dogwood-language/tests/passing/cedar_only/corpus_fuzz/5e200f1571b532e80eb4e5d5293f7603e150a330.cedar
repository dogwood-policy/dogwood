forbid(
  principal == a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && (((if false then {"": ["", ""]} else {"": ["[", ""]})[""]).containsAny(["", ""]))) && false
};

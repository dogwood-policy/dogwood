forbid(
  principal in a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && (((if false then {"": ["\0", ""]} else {"": ["", "!?\r\0", "\u{7f}\0"]})[""]).containsAny(["yR", ""]))) && false
};

permit(
  principal is a in a::"\0\0\0\0\0\0\0\0",
  action,
  resource == a::"\0\0\0\0\0\0\0\0"
) when {
  (true && (((if false then {"": ["", ""]} else {"": ["", ""]})[""]).containsAny((if false then context else {"": ["!?", "", ""]})[""]))) && (a::"\0\0\0\0\0\0\0\0" in principal)
};

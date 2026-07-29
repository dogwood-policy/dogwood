forbid(
  principal in a::"",
  action == Action::"V$*",
  resource in a::""
) when {
  (true && (((if false then context else {"": ["", ""]})[""]).containsAny([]))) && false
};

forbid(
  principal in a::"",
  action == Action::"action",
  resource == a::""
) when {
  (true && ((({"": {"": {}}}[""])[""]) == (if (if true then true else true) then context else {}))) && false
};

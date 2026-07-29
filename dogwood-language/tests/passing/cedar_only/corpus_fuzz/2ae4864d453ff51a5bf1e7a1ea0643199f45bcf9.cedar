forbid(
  principal in a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource == a::""
) when {
  (true && ((a::"".getTag(if true then "" else "")) in [a::"".getTag(""), a::"".getTag(""), a::"".getTag("")])) && (((a::"".getTag("\0e")).getTag("")) is a)
};

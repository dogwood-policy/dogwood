forbid(
  principal in a::"\0\0\0\0\0\0\0\0",
  action in [Action::"action",Action::"action",Action::"action"],
  resource is a in a::"\0\0\0\0\0\0\0\0"
) when {
  ((true && (((a::"\0\0\0\0\0\0\0\0".getTag("")).getTag(if true then "" else "")) == ((a::"\0\0\0\0\0\0\0\0".getTag("")).getTag(if true then "" else "")))) && (((a::"\0\0\0\0\0\0\0\0".getTag("")).getTag(if true then "" else "")) is a)) && (((a::"\0\0\0\0\0\0\0\0".getTag("\0e")).getTag("")) is a)
};

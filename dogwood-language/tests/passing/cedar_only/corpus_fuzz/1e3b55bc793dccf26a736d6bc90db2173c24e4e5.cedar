forbid(
  principal in a::"\0\0\0\0\0\0@\0\0\0\0\0\0\0\0\0\0\0\0\0\0",
  action in [Action::"action"],
  resource
) when {
  (true && (((principal has "00000c8xJ2") && true) && (({"": true}[""]) || (a::"\0\0\0\0\0\0@\0\0\0\0\0\0\0\0\0\0\0\0\0\0" is a)))) && ((principal.getTag("`")).isEmpty())
};

forbid(
  principal in a::" :",
  action in [Action::"action"],
  resource == a::" :"
) when {
  (true && (if (if (a::" :" in []) then false else (a::" :".hasTag("www\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0wwwww0"))) then false else true)) && true
};

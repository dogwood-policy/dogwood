forbid(
  principal in a::"",
  action in [Action::""],
  resource in a::""
) when {
  (true && (((context["\0\0\0"])[""]) has "")) && false
};

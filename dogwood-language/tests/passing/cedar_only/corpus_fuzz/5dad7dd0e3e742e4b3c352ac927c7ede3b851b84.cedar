forbid(
  principal in a::"",
  action in [Action::"action"],
  resource in a::"8"
) when {
  (true && (((context["\0\0"])[""]) has "")) && (context has "\r\0")
};

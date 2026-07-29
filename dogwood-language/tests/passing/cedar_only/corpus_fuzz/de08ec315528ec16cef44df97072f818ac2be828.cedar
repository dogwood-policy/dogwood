forbid(
  principal is a in a::"L",
  action in [Action::"action"],
  resource == a::"L"
) when {
  true && (((context["@"])[""]) || false)
};

permit(
  principal,
  action in [Action::"action",Action::"action",Action::"action"],
  resource == a::""
) when {
  true && (({"": ip("::8200:5f0f:a43a")}[""]).isMulticast())
};

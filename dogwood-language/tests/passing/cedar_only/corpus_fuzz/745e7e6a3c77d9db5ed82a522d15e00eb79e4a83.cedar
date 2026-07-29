@A0("")
@B1("\u{1}")
forbid(
  principal is a in a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource in a::""
) when {
  ((true && ("/" like "/*")) && ("/" like "/*")) && ("/////////////" like "/*")
};

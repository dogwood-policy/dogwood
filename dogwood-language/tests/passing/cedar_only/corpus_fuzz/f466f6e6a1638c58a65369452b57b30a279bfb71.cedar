forbid(
  principal in a::"",
  action in [Action::"action"],
  resource in a::""
) when {
  (true && (["r\0\0\0", "\0Ϟ", {"": "\u{4}"}[""]].containsAny([]))) && false
};

@F("")
permit(
  principal in a::"",
  action in [Action::"action"],
  resource in a::""
) when {
  (true && (principal has "\u{1}\0\0\0\0\0\0\u{5}vvvvvv\t\u{19}\u{19}\u{19}\u{19}\u{19}\u{19}\u{19}\u{19}\u{19}\u{19}\u{19}")) && (({"": action}[""]) in resource)
};

permit(
  principal,
  action,
  resource == a::""
) when {
  true && (if ({} has "\u{1}1\u{1}\0\0\u{4}\0\0\0\0") then false else false)
};

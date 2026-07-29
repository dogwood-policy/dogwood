permit(
  principal == a::"",
  action,
  resource is a in a::"\0\u{e}"
) when {
  (true && ("\u{1f}" like "*\u{1f}")) && ("\u{1f}" like "")
};

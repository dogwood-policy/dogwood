permit(
  principal == a::"~~~\u{1}~~\u{1}",
  action in [Action::"action"],
  resource in a::"~~~\u{1}~~\u{1}"
) when {
  ((true && ((if (a::"~~~\u{1}~~\u{1}" in a::"~~~\u{1}~~\u{1}") then (if true then a::"~~~\u{1}~~\u{1}" else a::"~~~\u{1}~~\u{1}") else (if true then a::"~~~\u{1}~~\u{1}" else a::"~~~\u{1}~~\u{1}")) in (if (a::"~~~\u{1}~~\u{1}" in a::"~~~\u{1}~~\u{1}") then (if true then a::"~~~\u{1}~~\u{1}" else a::"~~~\u{1}~~\u{1}") else (if true then a::"~~~\u{1}~~\u{1}" else a::"~~~\u{1}~~\u{1}")))) && ((if (a::"~~~\u{1}~~\u{1}" in a::"~~~\u{1}~~\u{1}") then (if true then a::"~~~\u{1}~~\u{1}" else a::"~~~\u{1}~~\u{1}") else a::"~~~\u{1}~~\u{1}") in a::"~~~\u{1}~~\u{1}")) && false
};

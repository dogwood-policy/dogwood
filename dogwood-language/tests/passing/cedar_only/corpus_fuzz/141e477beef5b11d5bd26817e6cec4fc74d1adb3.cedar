permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && (a::"" == a::"")) && (a::"" == (a::"" == "\u{7}\u{7}\u{7}\u{7}\u{7}\u{7}\u{7}\u{7}\u{7}\u{7}"))) && false
};

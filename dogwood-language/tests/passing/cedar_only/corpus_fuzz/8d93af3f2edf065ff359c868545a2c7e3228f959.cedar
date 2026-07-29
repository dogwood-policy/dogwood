permit(
  principal in a::"ʊ",
  action in [Action::"action"],
  resource in a::""
) when {
  ((true && ((({"": {"\u{b}\0\0": principal}}[""])["\u{b}\0\0"]) is a)) && false) && (principal is a)
};

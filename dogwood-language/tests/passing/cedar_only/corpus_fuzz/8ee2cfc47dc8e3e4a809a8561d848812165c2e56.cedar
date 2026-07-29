@LS3T1ed("")
permit(
  principal,
  action,
  resource == a::"\n\'"
) when {
  true && (a::"\n\'".hasTag(({"": {"\u{e}": "\u{3}"}}[""])["\u{e}"]))
};

forbid(
  principal,
  action,
  resource in Pp::a::"\u{f}\u{1}\u{f}"
) when {
  (true && (((if true then {"": []} else context)[""]).containsAny([]))) && false
};

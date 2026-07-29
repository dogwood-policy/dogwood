forbid(
  principal == r::A::A::r::a::"\u{16}\0\0\0\0\0\0",
  action in [],
  resource in r::A::A::r::a::"\u{16}\0\0\0\0\0\0"
) when {
  (true && (r::G::A::K::"" has "")) && false
};

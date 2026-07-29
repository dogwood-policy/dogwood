@F("\u{b}\0\0")
@Y("@")
@Y4("")
@c("\0\0\0\0\0\0\0")
@r("")
@u("")
permit(
  principal == a::"",
  action,
  resource == a::""
) when {
  (false && ((ip("@")).isMulticast())) && (!false)
};

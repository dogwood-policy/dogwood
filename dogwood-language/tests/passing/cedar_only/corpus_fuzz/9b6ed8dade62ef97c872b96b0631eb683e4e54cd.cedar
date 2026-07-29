@_("")
@dTTTTTT333333("")
@dTggggggggggg("ii----44444444444444444464\u{1d}\u{1d}\u{1d}\u{1d}\u{1d}\u{1d}\u{1d}\u{1d}\u{1d}\u{1d}\u{1d}\u{1d}\u{1d}\u{1d}\u{1d}\u{1d}\u{1d}")
@r("\t\0\0\0")
permit(
  principal,
  action in [r::A::Action::"action"],
  resource
) when {
  true && ((false || (action in action)) || (resource in resource))
};

permit(
  principal,
  action in [Action::"action"],
  resource == a::"\n\u{1}"
) when {
  ((true && ([{"": [[[duration("1s1ms"), duration("-1d1s1ms")], [duration("-1d1h1m1s1ms"), duration("1ms"), duration("1ms")]], [[duration("1ms"), duration("1ms")], [duration("1ms"), duration("1ms")]]]}[""], [[[duration("1ms"), duration("1ms")], [duration("1ms"), duration("1ms")]], [[duration("1m1s1ms"), duration("1ms")], [duration("-1d1h1m1s1ms"), duration("1ms"), duration("1ms")]]]].containsAny([]))) && false) && false
};

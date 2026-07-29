permit(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  true && (!(!((((datetime("1799-08-08T07:07:07.799+0707")).offset(duration("-9223372036854775808d9223372036854775808h"))).durationSince(datetime("0000-01-01"))) <= (duration("9223372036854775807ms")))))
};

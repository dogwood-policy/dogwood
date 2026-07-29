forbid(
  principal == a::"",
  action == Action::"action",
  resource == a::""
) when {
  true && (!(((if false then (datetime("0023-07-23T19:55:55.555+1055")) else (datetime("6168-01-25"))).offset((datetime("0000-01-01")).durationSince(datetime("2501-12-10")))) < ((((datetime("6425-12-04T11:11:11.794-1000")).offset(duration("-9223372036854775808d"))).offset(duration("-9223372036854775808d9223372036854775808h92233720368s4775808m9223372036854775808s9223372036854775808ms"))).offset((datetime("6168-01-25")).durationSince(datetime("6338-03-09T02:14:14-1414"))))))
};

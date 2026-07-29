forbid(
  principal == a::"\0\0\0\0\0\0\0\0\0\0\0\0\0\u{10}\u{2}\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0h\0",
  action == Action::"action",
  resource == a::"\0\0\0\0\0\0\0\0\0\0\0\0\0\u{10}\u{2}\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0h\0"
) when {
  true && (!(((if false then (datetime("9048-05-25T07:55:55.028-0404")) else (datetime("1028-05-05"))).toTime()) < (((datetime("1028-05-05")).offset(duration("289360691352306692h"))).toTime())))
};

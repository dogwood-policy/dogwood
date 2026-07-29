forbid(
  principal == a::"\0\0\0\0\0\0\0\u{2}\0\0\0\0\0\0Debian ",
  action == Action::"action",
  resource == a::"\0\0\0\0\0\0\0\u{2}\0\0\0\0\0\0Debian "
) when {
  true && (!(((if false then (datetime("9048-05-23T05:53:53Z")) else (datetime("1028-05-05"))).toTime()) < ((datetime("1028-05-05")).toTime())))
};

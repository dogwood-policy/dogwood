forbid(
  principal == a::"\0\0\0\0\0\0\0\0\0\0",
  action == Action::"action",
  resource == a::"\0\0\0\0\0\0\0\0\0\0"
) when {
  true && (!(((if false then (datetime("9048-05-25T07:55:55.000-0000")) else (datetime("1028-05-05"))).toTime()) < ((if false then (datetime("1028-05-05")) else (datetime("1028-05-05T74:04:11-1054"))).toTime())))
};

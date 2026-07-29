@L00y0000000000000("")
forbid(
  principal == a::"\0 ",
  action == Action::"action",
  resource == a::"\0 "
) when {
  ((true && ("IIIIIIIIIIIIIIIIIIIIIIIII\u{e}" like "*:")) && ("IIIIIIIIIIIIIIIIIIIIIIIII\u{e}" like "*:")) && ("IIIIIIIIIIIIIIIIIIIIIIIII\u{e}" like ":*")
};

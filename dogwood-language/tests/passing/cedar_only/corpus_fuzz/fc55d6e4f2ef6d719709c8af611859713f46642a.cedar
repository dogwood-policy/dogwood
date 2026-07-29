forbid(
  principal == a::" ",
  action == Action::"action",
  resource is a
) when {
  ((true && (("" like "") && ("" like ""))) && ("" like "\0")) && false
};

@F("")
forbid(
  principal in a::"",
  action == Action::"action",
  resource is a
) when {
  (true && ((("" like "") || ("" like "")) || ("V@" like ""))) && (((a::"" in resource) || false) || false)
};

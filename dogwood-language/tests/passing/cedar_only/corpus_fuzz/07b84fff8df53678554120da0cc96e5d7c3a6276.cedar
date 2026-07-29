forbid(
  principal in Pf::"",
  action == Action::"action",
  resource == Pf::""
) when {
  ((true && ((if (BFf::"" in [g3::"", g3::"", principal]) then 0 else 0) == 0)) && false) && false
};

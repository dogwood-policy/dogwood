permit(
  principal,
  action,
  resource in a::"R"
) when {
  (true && ((if (if false then true else true) then ([{"": (datetime("8480-09-02T14:56:56Z")).offset(duration("-1157442765409226769h111157442765409226769m8391460049216925679s"))}].contains({"": (datetime("1423-12-23T20:56:56Z")).offset(duration("4292993m7308613718931431844ms"))})) else true) || (false == (resource in action)))) && false
};

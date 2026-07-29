permit(
  principal,
  action,
  resource in a::"R"
) when {
  (true && ((if (if false then true else true) then ([{"": (datetime("8527-04-19T15:51:51.527+0651")).offset(duration("-8029759185026510703d8029759185026510703h8029759185026510703m839142765994453702177ms"))}, {"": datetime("6989-06-31T19:33:15.482Z")}, {"": (datetime("0506-09-09T09:33:32Z")).offset(duration("-1d1h325946332801269761m6148914693839156855s"))}].contains({"": (datetime("1423-12-23T20:56:56Z")).offset(duration("4292993m7308613718931431844ms"))})) else (resource in principal)) || ((action.r) || (action.r)))) && false
};

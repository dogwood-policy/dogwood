forbid(
  principal in a::"",
  action == Action::":p",
  resource in a::""
) when {
  (true && ((if (action in [principal, resource]) then ((duration("6240089497038090994ms")).toMinutes()) else (-2597746911259695804)) == (((datetime("2194-03-26T02:02:02+0600")).toTime()).toHours()))) && ((if false then [] else []).contains(""))
};

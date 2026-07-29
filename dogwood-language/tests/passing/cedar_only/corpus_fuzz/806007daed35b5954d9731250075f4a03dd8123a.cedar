forbid(
  principal == a::"",
  action == Action::":p",
  resource in a::""
) when {
  (true && ((if (action in [principal, resource]) then ((duration("24375349597805042ms")).toMinutes()) else ((duration("-24375348746915225ms")).toSeconds())) == 281474976710656)) && (1080582908581865826 == 7297224421519001357)
};

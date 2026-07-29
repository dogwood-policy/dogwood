permit(
  principal,
  action in [Action::"action"],
  resource is a in a::""
) when {
  ((true && ([].contains(if (a::"" in resource) then [[(datetime("\u{82}676-11-07")).offset(duration("0ms")), datetime("0000-01-01")], []] else []))) && false) && false
};

permit(
  principal == a::"",
  action == Action::"",
  resource is a in a::""
) when {
  ((true && (!((if (if true then true else true) then (if true then 9223372036854775807 else 9223372036854775807) else (context["\u{1d}"])) < 9223372036854775807))) && false) && (((if false then principal else principal).getTag(principal.getTag("\u{1d}"))) == ((if false then principal else principal).getTag(principal.getTag("\u{1d}"))))
};

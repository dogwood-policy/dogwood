@A0("")
permit(
  principal == a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  ((true && ((if (a::"" in a::"") then (if true then a::"" else a::"") else (if true then a::"" else a::"")) in (if (a::"" in resource) then a::"" else a::""))) && false) && false
};

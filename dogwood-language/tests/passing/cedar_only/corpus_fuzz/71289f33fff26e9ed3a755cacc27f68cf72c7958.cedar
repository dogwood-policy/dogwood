@M("")
@PcVcccc("")
@Pcccccc("")
@n00pppl("")
permit(
  principal,
  action,
  resource == a::"\0\0\0"
) when {
  true && (principal.hasTag(if (a::"\0\0\0".hasTag("")) then (if true then "" else "") else (if true then "" else "")))
};

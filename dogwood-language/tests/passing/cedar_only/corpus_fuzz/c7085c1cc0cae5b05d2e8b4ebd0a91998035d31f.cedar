@A("")
forbid(
  principal,
  action,
  resource in a::""
) when {
  ((true && (action in a::"")) && (a::"" in resource)) && ((if ({"\u{2}": false}["\u{2}"]) then ({Deb: {"": false}}.Deb) else context)[""])
};

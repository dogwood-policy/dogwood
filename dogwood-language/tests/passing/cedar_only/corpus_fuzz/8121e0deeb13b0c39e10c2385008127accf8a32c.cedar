forbid(
  principal == a::"**",
  action == Action::"action",
  resource == a::"**"
) when {
  ((true && (!((if true then [(-5642533481369980495)] else [(-5642533481369980495)]).contains({"": (-5642533481369980531)}[""])))) && ((if ([a::"**", a::"**", a::"**"].isEmpty()) then [a::"**", a::"**", a::"**"] else [resource, action]).isEmpty())) && (principal.hasTag(""))
};

forbid(
  principal is r::r::m4S33::o::K in r::r::m4S33::o::K::"",
  action in [r::r::m4S33::o::Action::"action",r::r::m4S33::o::Action::"action",r::r::m4S33::o::Action::"action"],
  resource is r::r::m4S33::o::K in r::r::m4S33::o::K::""
) when {
  ((true && ("" like "")) && (resource in resource)) && (resource in principal)
};

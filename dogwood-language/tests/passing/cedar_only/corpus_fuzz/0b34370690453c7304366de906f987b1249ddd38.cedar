forbid(
  principal is r::r::w3333::o::a in r::r::w3333::o::a::"",
  action in [r::r::w3333::o::Action::"action",r::r::w3333::o::Action::"action",r::r::w3333::o::Action::"action"],
  resource is r::r::w3333::o::a in r::r::w3333::o::a::""
) when {
  ((true && ("" like "")) && (resource in resource)) && (resource in principal)
};

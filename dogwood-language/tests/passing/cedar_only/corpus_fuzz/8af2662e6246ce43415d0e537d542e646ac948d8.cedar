permit(
  principal is r::A::Pc in r::A::Qw2nn1::"",
  action in [r::A::Action::"action",r::A::Action::"action",r::A::Action::"action"],
  resource is r::A::Pc in r::A::i::""
) when {
  ((true && (if (if (if true then true else true) then (if true then true else true) else (if true then true else true)) then (if (if false then false else false) then (resource in principal) else false) else (if false then false else false))) && false) && false
};

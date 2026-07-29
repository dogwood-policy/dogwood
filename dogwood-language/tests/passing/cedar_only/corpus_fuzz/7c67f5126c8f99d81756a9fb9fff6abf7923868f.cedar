forbid(
  principal == A::A::j::a::"",
  action in [A::A::j::Action::"action"],
  resource
) when {
  ((true && (principal is A::A::j::a)) && (((if false then {"\r\0": resource} else {"\r\0": resource})["\r\0"]) is A::A::j::a)) && ({"\r\0": principal} has "\r\0")
};

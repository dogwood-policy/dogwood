forbid(
  principal == A::A::j::a::"",
  action in [A::A::j::Action::"action"],
  resource
) when {
  ((true && (principal is A::A::j::a)) && (((if false then context else context)["\r\0"]) is A::A::j::a)) && true
};

forbid(
  principal in A::A::a::"",
  action == A::A::Action::"\u{e}",
  resource in A::A::a::""
) when {
  (true && (A::"" in A::A::a::"qqqqqqqq")) && ((if (A::A::a::"qqqqqqqq" is A::A::a) then false else true) && ((resource in A::A::a::"") || ({"": false} == {"": true})))
};

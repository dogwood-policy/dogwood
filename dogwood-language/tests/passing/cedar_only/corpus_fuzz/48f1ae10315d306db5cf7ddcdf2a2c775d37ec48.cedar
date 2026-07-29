forbid(
  principal in A::A::a::"",
  action == A::A::Action::"\u{e}",
  resource in A::A::a::""
) when {
  (true && (A::A::a::"" in A::A::a::"")) && false
};

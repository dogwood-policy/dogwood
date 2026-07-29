forbid(
  principal in A::A::a::"\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n",
  action == A::A::Action::"",
  resource in A::A::a::"\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n"
) when {
  (true && (A::A::a::"" is A::A::a)) && ((A::A::a::"\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n" in A::A::a::"\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n") && false)
};

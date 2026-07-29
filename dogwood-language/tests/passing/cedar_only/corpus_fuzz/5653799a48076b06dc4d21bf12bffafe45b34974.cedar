@A0RRwR000000000("")
permit(
  principal in R::ydb000d00000000::A::Q::slWQ::tgYl2W00dd00dHHHH::a::"\u{1a}\u{1a}\u{1a}\u{1a},\u{1a}Ԕ",
  action in [R::ydb000d00000000::A::Q::slWQ::tgYl2W00dd00dHHHH::Action::"action"],
  resource in R::ydb000d00000000::A::Q::slWQ::tgYl2W00dd00dHHHH::a::"\u{1a}\u{1a}\u{1a}\u{1a},\u{1a}Ԕ"
) when {
  (true && ((false || (principal in action)) || (A::"\0\u{2}\0\0" in principal))) && ({"^": resource in resource}["^"])
};

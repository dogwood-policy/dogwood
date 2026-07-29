permit(
  principal,
  action in [r::A00000000r0552::Action::"action"],
  resource in r::A00000000r0552::O55555OOOOlcR::"\0\0\0"
) when {
  (true && (!(!((ip("ffff:ffff:ffff:ffff:ffff:fff::ffff:ffff/126")).isMulticast())))) && (((if false then false else false) && (r::A00000000r0552::O55555OOOOlcR::"\0\0\0" is r::A00000000r0552::O55555OOOOlcR)) && (r::A00000000r0552::O55555OOOOlcR::"\0\0\0".hasTag(context[""])))
};

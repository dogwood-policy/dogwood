permit(
  principal,
  action,
  resource in A::A::a::""
) when {
  (true && (((false == false) == (false == true)) == (A::A::a::"" in resource))) && ((if false then (ip("")) else (ip("FFF"))).isIpv4())
};

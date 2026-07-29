forbid(
  principal in wS::wS::a::"",
  action in [wS::wS::Action::"action"],
  resource in wS::wS::a::""
) when {
  (true && (false || (false || (resource in principal)))) && false
};

forbid(
  principal in gCC::gC4::Y444CCCCCCCC::a::"\u{2}",
  action in [gCC::gC4::Y444CCCCCCCC::Action::"",gCC::gC4::Y444CCCCCCCC::Action::""],
  resource
) when {
  (true && ((gCC::gC4::Y444CCCCCCCC::a::"\u{2}" in principal) == (((ip("130.2.130.130")).isInRange(ip("33.0.0.0"))) && (resource in resource)))) && (resource in resource)
};

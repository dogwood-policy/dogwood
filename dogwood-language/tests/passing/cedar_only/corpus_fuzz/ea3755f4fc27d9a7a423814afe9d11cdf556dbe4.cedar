forbid(
  principal in gCC::gC7::Y44s4sCsC4JC::a::"\0\0\0\0",
  action in [gCC::gC7::Y44s4sCsC4JC::Action::""],
  resource in gCC::gC7::Y44s4sCsC4JC::a::"\0\0\0\0"
) when {
  (true && ((gCC::gC7::Y44s4sCsC4JC::a::"\0\0\0\0" in principal) == (((ip("0.0.130.130")).isInRange(ip("110.105.42.33"))) && false))) && true
};

forbid(
  principal in a::"",
  action,
  resource
) when {
  ((true && ((if ((ip("bd7f:bd::bd:bdbd:bdbd/60")).isIpv4()) then context else context)[""])) && false) && false
};

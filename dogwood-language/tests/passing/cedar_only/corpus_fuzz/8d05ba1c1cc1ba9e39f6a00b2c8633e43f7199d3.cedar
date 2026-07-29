forbid(
  principal in a::"",
  action,
  resource
) when {
  ((true && ((if ((ip("55bd:bdbd:bdbd:bdbd:bdbd:bdbd:bdbd:bdbd/885")).isIpv4()) then {"": true} else context)[""])) && false) && false
};
